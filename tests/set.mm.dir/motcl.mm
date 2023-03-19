include "wf1o.mm"
include "wf.mm"
include "motf1o.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnd.mm"

theorem motcl
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )
  assume motco.2: |- ( ph -> F e. ( G Ismt G ) )
  assume motcl.a: |- ( ph -> A e. P )


  assert |- ( ph -> ( F ` A ) e. P )

  proof
    wph
    cP
    cP
    cA
    cF
    wph
    cP
    cP
    cF
    wf1o
    cP
    cP
    cF
    wf
    wph
    cP
    cF
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    motgrp.1
    motco.2
    motf1o
    cP
    cP
    cF
    f1of
    syl
    motcl.a
    ffvelrnd
end
