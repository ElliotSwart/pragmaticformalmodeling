---
layout: default
parent: Business Logic
title: Principal Engineer saves the day
nav_order: 3

states:
    - name: All States		
      total: 7995363	
      distinct: 1115416	


---

{% include title_toc.md %}

## Your bio

At the age of three you killed Python and wore it as a hat. You have a resume a mile long from all your successfully completed projects, and a thousand yard stare from the ones you couldn't save. You'll probably be a programmer forever, if only because semi-pro competitive tap dance just doesn't pay the bills. 

## The assignment

1. Simplify the junior developer's solution.
2. Use the model checker to verify that your elegant solution is, as Einstein would say, "as simple as possible but no simpler."

## Modeling the solution

Using the model checker as a guide, you refactor the solution to denormalize the data model somewhat. Whenever possible, you convert logic to simple database transactions.

{% include code.html path="specprincipal" snippet="principal"%}

You use the model checker periodically to ensure that the simplified design still hit requirements. Once you're confident the design is sufficiently simple, you run a final test on your solution.

## Verifying the solution

It passes.

{% include states.md states=page.states namespace="principal" modelcfg="specprincipal.cfg"%}

Time to start building!

## Design and its effect on automated testing

When testing requirements, the standard approach is to map each requirement to one or more specific programmatic tests. For straightforward requirements with immediate triggers and effects, this is not a problem. An integration test can trigger the relevant action and observe the effect. For more complex requirements, those that are more woven into the design, this is challenging. Generally, you trace those requirements to a design document which describes how they are to be fulfilled. Senior engineers and/or architects sign off that the design meets the requirements. Then tests are planned to show conformance with the design.

Formal modeling helps us with this process in two ways:
- The requirements can be explicitly mapped to a model
- A specific design model can be tested against the requirement model

The requirements can therefore be straightforwardly verified to be implemented by the design model. It's far easier to test for sub-system and component compliance with the design model than with textual requirements. Automated requirement testing can often turn into glorified regression tests if a team is not careful. By testing to the design model instead, a team can ensure that critical system characteristics are maintained without over-specifying behavior.

## Retrospective

Key takeaways from this series:
- Precise requirements documents can be modeled formally.
- Sloppy logic and design are much more apparent in modeled designs than in code.
- Modeled specifications allow you to refactor business logic confidently.
- Modeling business requirements means that you can focus unit and integration testing on testing critical behavior.



| Next: [You made it to the end! Time to learn TLA+](../../learning-material) |