---
layout: default
parent: Business Logic
title: Junior Developer tries their best
nav_order: 2
v1:
  align: left
  2:
    note: A trial starts, but user can still subscribe.
  3:
    note: A month passes, converting trial into a full subscription. Now you shouldn't be able to start a subscription, but you still can.
v2:
  align: left
  2: 
    note: Subscription states.
  3:
    note: Month passes, and you assume user should be billed.
  4:
    note: User cancels subscription before monthly billing could take place.
  5:
    note: User is not billed.
  6:
    note: A month passes, and our system hasn't billed. Out of compliance.
v3:
    - name: All States		
      total: 772157
      distinct: 153504	
---

{% include title_toc.md %}

## Introduction

### Your bio

You recently graduated from a good computer science program. Not only do you have a firm grasp on CS fundamentals, you've also taken electives in operating system and compiler design. None of that has been much help here, though. You keep waiting for someone to ask you to traverse a tree or write a new lexer for C, but you're starting to fear that day will never come.


### Your assignment
1. Try to create a solution that implements the Enterprise Architect's specification.
2. Use the model checker to get your solution working.

## The first attempt
### Modeling
_Note: We are assuming the junior programmer is fully competent in TLA+ and code style. Only the architectural and/or requirements knowledge will be lacking._

You start with a simple and clean solution that meets the requirements as you understood them:

{% include code.html path="specjuniorv1" snippet="juniorv1snippet"%}

### Verification
Your solution does not hold up under test.
{% include trace.html traceconfig=page.v1 constraint="Invariant StartSubscriptionAccessControl is violated." trace=site.data.business-logic.junior-dev.v1 modelcfg="specjuniorv1.cfg"%}

There are basic logical errors that need to be fixed.

## The second attempt
### Modeling
For this next attempt you work through all the standard logical errors around access control.

{% include code.html path="specjuniorv2" snippet="juniorv2snippet" %}

### Verification

You test again, running into a billing issue.

{% include trace.html traceconfig=page.v2 constraint="Invariant SubscribedUsersBilledStartOfMonth is violated." trace=site.data.business-logic.junior-dev.v2 modelcfg="specjuniorv2.cfg" %}

This is a much more complex business logic error, and it's of the sort that conventional testing may not catch.

## The working attempt
### Modeling
In the final attempt there you add significantly more billing logic.

{% include code.html path="specjuniorv3" snippet="juniorv3snippet" modelcfg="specjuniorv3.cfg"%}

The code is starting to look like a nightmare, but hopefully it will work.

### Verification
Testing it leads to success!

{% include states.md states=page.v3 namespace="junior" modelcfg="specjuniorv3.cfg"%}

## Next steps
So you've gotten a solution working, but frankly, it looks like it'll be a nightmare to implement. Nested if statements all over the place. The database schema is sloppy. It's time to ask for help.

> _Note: A valid criticism of the above would be that no one would model business logic like that. And it's true, no one would model something that badly. But people push solutions much worse than this one to production every day. Maybe if they took the time to model, they wouldn't._

<br><br>

| Next: [ Principal Engineer saves the day](../principal-eng) |