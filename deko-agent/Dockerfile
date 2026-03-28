FROM python:3.12-slim

WORKDIR /app

COPY deko_agent.py /app/deko_agent.py

RUN chmod +x /app/deko_agent.py

ENTRYPOINT ["python3", "/app/deko_agent.py"]
