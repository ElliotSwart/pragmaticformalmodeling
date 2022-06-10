---
layout: default
title: Business Logic
nav_order: 4
has_children: true
has_toc: false
---

{% include title_toc.md %}

## Introduction

We've previously used TLA+ mostly for distributed systems problems, but you can also used it to model business logic. First we'll go from requirements to a mathematical specification. Then we'll show two implementations of the specification that lead to the satisfaction of the scenario requirements. Those implementations will be the model for the business logic code to be developed. We'll demonstrate how formal specifications can be used to perform tests of implementations, as well as high confidence refactors. 

## The scenario

A software design/consulting firm has been contracted to build a website that allows users to watch instructional workout videos online. Let's say it's called MuscleMovies.com.

It was founded by former gym and magazine executives, so they have lots of ideas on how to maximize their profits _(or gains, if you will)_. We're talking trial memberships that convert into paid memberships, payment processing and cancellation penalties!

In the following pages, we'll get to be three different people:
- [The Enterprise Architect](enterprise-architect): who distills the requirements into standard form, makes the architectural choices and writes the formal interface specification.
- [The Junior Developer](junior-dev): who is dropped into this project and struggles through the requirements piece by piece.
- [The Principal Engineer](principal-eng): who jumps in and saves the day by reimplementing the requirements in a cleaner fashion.

It's basically Rashomon, but presented clearly and in chronological order. And with higher stakes, at least according to the MuscleMovies.com CEO.

> _Don't worry: despite the tone, we're going rigorous with requirements._

<br><br>

| Next: [Enterprise Architect gets us started](enterprise-architect) |