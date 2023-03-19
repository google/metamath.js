include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cco1.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantl.mm"
include "nn0ex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "elmap.mm"
include "sylibr.mm"
include "eqidd.mm"
include "cmpl.mm"
include "eqid.mm"
include "psr1baslem.mm"
include "ply1mpl0.mm"
include "a1i.mm"
include "ringgrp.mm"
include "mpl0.mm"
include "fconstmpt.mm"
include "syl6eq.mm"
include "wceq.mm"
include "fmptco.mm"
include "cbs.mm"
include "ply1ring.mm"
include "ring0cl.mm"
include "coe1fval2.mm"
include "3syl.mm"
include "3eqtr4d.mm"

theorem coe1z
  let cP: class P
  let cR: class R
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume coe1z.p: |- P = ( Poly1 ` R )
  assume coe1z.z: |- .0. = ( 0g ` P )
  assume coe1z.y: |- Y = ( 0g ` R )


  assert |- ( R e. Ring -> ( coe1 ` .0. ) = ( NN0 X. { Y } ) )

  proof
    cR
    crg
    wcel
    #
    c.0
    va
    cn0
    c1o
    va
    cv
    #
    csn
    cxp
    #
    cmpt
    #
    ccom
    #
    va
    cn0
    cY
    cmpt
    #
    c.0
    cco1
    cfv
    #
    cn0
    cY
    csn
    #
    cxp
    #
    @0
    va
    vb
    cn0
    cn0
    c1o
    cmap
    co
    #
    @2
    cY
    cY
    @3
    c.0
    @0
    @1
    cn0
    wcel
    #
    wa
    c1o
    cn0
    @2
    wf
    #
    @2
    @9
    wcel
    @10
    @11
    @0
    c1o
    @1
    cn0
    fconst6g
    adantl
    cn0
    c1o
    @2
    nn0ex
    c1o
    con0
    1on
    elexi
    elmap
    sylibr
    @0
    @3
    eqidd
    @0
    c.0
    @9
    @7
    cxp
    vb
    @9
    cY
    cmpt
    @0
    @9
    c1o
    cR
    cmpl
    co
    #
    cR
    vc
    c1o
    cY
    con0
    c.0
    @12
    eqid
    #
    vc
    psr1baslem
    coe1z.y
    cP
    cR
    @12
    c.0
    @13
    coe1z.p
    coe1z.z
    ply1mpl0
    c1o
    con0
    wcel
    @0
    1on
    a1i
    cR
    ringgrp
    mpl0
    vb
    @9
    cY
    fconstmpt
    syl6eq
    vb
    cv
    @2
    wceq
    cY
    eqidd
    fmptco
    @0
    cP
    crg
    wcel
    c.0
    cP
    cbs
    cfv
    #
    wcel
    @6
    @4
    wceq
    cP
    cR
    coe1z.p
    ply1ring
    @14
    cP
    c.0
    @14
    eqid
    #
    coe1z.z
    ring0cl
    va
    @6
    @14
    cP
    cR
    c.0
    @3
    @6
    eqid
    @15
    coe1z.p
    @3
    eqid
    coe1fval2
    3syl
    @8
    @5
    wceq
    @0
    va
    cn0
    cY
    fconstmpt
    a1i
    3eqtr4d
end
