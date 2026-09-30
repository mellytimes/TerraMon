# TerraMon

Little TUI I made to babysit my Terraria server on Proxmox. Auto-restarts it, fixes DuckDNS when my IP changes, and downloads new server versions for me.

## Install

```bash
wget -O terramon.py https://gist.githubusercontent.com/mellytimes/c935fecff360201e7375775b8d377194/raw/terramon.py
```

## Run

```bash
screen -S terramon
python3 terramon.py
```

Detach with `Ctrl+A` then `D`. The Terraria server keeps running even if you quit TerraMon.

## Requirements

Python 3 and `screen`:

```bash
apt install -y python3 screen wget
```
