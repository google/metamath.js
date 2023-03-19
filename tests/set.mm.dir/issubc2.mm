include "cdm.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "fndm.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6req.mm"
include "issubc.mm"

theorem issubc2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cJ: class J
  let vc: setvar c
  let vj: setvar j
  let vs: setvar s
  assume issubc.h: |- H = ( Homf ` C )
  assume issubc.i: |- .1. = ( Id ` C )
  assume issubc.o: |- .x. = ( comp ` C )
  assume issubc.c: |- ( ph -> C e. Cat )
  assume issubc2.a: |- ( ph -> J Fn ( S X. S ) )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint C f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S f
  disjoint S g
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c s
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint C c
  disjoint f j
  disjoint f s
  disjoint g j
  disjoint g s
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint C j
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint J c
  disjoint J j
  disjoint J s
  disjoint S c
  disjoint S j
  disjoint S s
  disjoint .1. c
  disjoint .1. j
  disjoint .1. s
  disjoint H c
  disjoint H j
  disjoint .x. c
  disjoint .x. j
  disjoint .x. s
  assert |- ( ph -> ( J e. ( Subcat ` C ) <-> ( J C_cat H /\ A. x e. S ( ( .1. ` x ) e. ( x J x ) /\ A. y e. S A. z e. S A. f e. ( x J y ) A. g e. ( y J z ) ( g ( <. x , y >. .x. z ) f ) e. ( x J z ) ) ) ) )

  proof
    wph
    vx
    vy
    vz
    cC
    cS
    c.x
    c.1
    vf
    vg
    cH
    cJ
    issubc.h
    issubc.i
    issubc.o
    issubc.c
    wph
    cJ
    cdm
    #
    cdm
    cS
    cS
    cxp
    #
    cdm
    cS
    wph
    @0
    @1
    wph
    cJ
    @1
    wfn
    @0
    @1
    wceq
    issubc2.a
    @1
    cJ
    fndm
    syl
    dmeqd
    cS
    dmxpid
    syl6req
    issubc
end
