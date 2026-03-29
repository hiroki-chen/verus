#![feature(allocator_api)]

use deko_policy_format::{
    decode_borrowed_lattice_v1_blob, decode_policy_blob_header, encode_lattice_v1_blob,
    PolicyBlobKind, POLICY_FORMAT_MAGIC, POLICY_FORMAT_VERSION,
};

fn build_lattice_blob() -> Vec<u8> {
    let levels = [b"public".as_slice(), b"orders_internal".as_slice(), b"orders_db".as_slice()];
    let relations = [(0u32, 1u32), (1u32, 2u32)];
    encode_lattice_v1_blob(&levels, &relations, 0, 2)
        .expect("lattice encoder should produce a valid blob")
}

fn main() {
    let blob = build_lattice_blob();

    let (header, payload) =
        decode_policy_blob_header(&blob).expect("policy blob header should decode");
    assert_eq!(header.magic, POLICY_FORMAT_MAGIC);
    assert_eq!(header.version, POLICY_FORMAT_VERSION);
    assert_eq!(header.kind, PolicyBlobKind::LatticeV1 as u16);
    assert_eq!(payload.len(), header.payload_len as usize);

    let borrowed =
        decode_borrowed_lattice_v1_blob(payload).expect("borrowed lattice blob should decode");

    assert_eq!(borrowed.header.level_count, 3);
    assert_eq!(borrowed.header.relation_count, 2);
    assert_eq!(borrowed.header.bot_level_idx, 0);
    assert_eq!(borrowed.header.top_level_idx, 2);
    assert_eq!(borrowed.level_bytes(0).unwrap(), b"public");
    assert_eq!(borrowed.level_bytes(1).unwrap(), b"orders_internal");
    assert_eq!(borrowed.level_bytes(2).unwrap(), b"orders_db");

    let rel0 = borrowed.relation_ref(0).expect("relation 0 should decode");
    assert_eq!(rel0.lhs_level_idx, 0);
    assert_eq!(rel0.rhs_level_idx, 1);

    let rel1 = borrowed.relation_ref(1).expect("relation 1 should decode");
    assert_eq!(rel1.lhs_level_idx, 1);
    assert_eq!(rel1.rhs_level_idx, 2);

    println!("policy_blob_parse: ok");
}
