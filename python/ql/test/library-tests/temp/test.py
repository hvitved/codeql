def source():
    return "boo"

def sink(val):
    print(val)

def sink2(**kwargs):
    print(kwargs["key"])

def middleman(**kwargs):
    sink(kwargs["key"])

# sanity check, is not flagged
sink(source())

# named arg through helper, is flagged
middleman(key=source())

# temporary dictionary storage, is flagged
a = {}
a["key"] = source()
sink(a["key"])

# passed through kwargs, is flagged
middleman(**a)

# passed as kwargs, is not flagged
sink2(**a)