<div class="requirements" markdown="1">

| ID | Requirement | 
|:-------------|:------------------|{% for requirement in include.requirements %}{% assign reqId = forloop.index %}
| {{reqId}} | {{requirement.text}} | {% for subrequirement in requirement.sub%}{% assign subId = forloop.index %} 
| {{reqId}}.{{subId}} |&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;{{subrequirement.text}} |{% for subsub in subrequirement.sub%}{% assign subsubId = forloop.index %}
| {{reqId}}.{{subId}}.{{subsubId}} |&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;{{subsub.text}} |{% endfor %}{% endfor %}{% endfor %}

</div>