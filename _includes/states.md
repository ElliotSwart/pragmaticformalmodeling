{% assign namespace = include.namespace %}
| <a href="#{{namespace}}-end">Next Section</a> | {% if include.model %} <a href="{{include.model}}">Download Model</a> |{% endif %} {% if include.modelcfg %} <a href="{{include.modelcfg}}">Download Configuration</a> |{% endif %}

| State Name | Total States | Distinct States |
|:-------------|:------------------|:------|
{% for state in include.states %}| {{state.name}} | {{state.total}} | {{state.distinct}} |
{% endfor %}

<div id="{{namespace}}-end"></div>