include "wcel.mm"
include "crefld.mm"
include "cfrlm.mm"
include "co.mm"
include "ctch.mm"
include "cfv.mm"
include "cnm.mm"
include "cbs.mm"
include "cv.mm"
include "cip.mm"
include "csqrt.mm"
include "cmpt.mm"
include "c2.mm"
include "cexp.mm"
include "cgsu.mm"
include "clmod.mm"
include "cgrp.mm"
include "wceq.mm"
include "crg.mm"
include "csr.mm"
include "recrng.mm"
include "srngring.mm"
include "ax-mp.mm"
include "eqid.mm"
include "frlmlmod.mm"
include "mpan.mm"
include "lmodgrp.mm"
include "tchnmfval.mm"
include "3syl.mm"
include "rrxval.mm"
include "fveq2d.mm"
include "tchbas.mm"
include "3eqtr4g.mm"
include "wa.mm"
include "cr.mm"
include "cmap.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "rrxbase.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "sselda.mm"
include "cmul.mm"
include "cvv.mm"
include "cmpt2.mm"
include "rrxip.mm"
include "tchip.mm"
include "a1i.mm"
include "3eqtr4rd.mm"
include "adantr.mm"
include "simprl.mm"
include "fveq1d.mm"
include "simprr.mm"
include "oveq12d.mm"
include "cc.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "adantlr.mm"
include "sqvald.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "simpr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "syldan.mm"
include "eqcomd.mm"
include "mpteq12dva.mm"

theorem rrxnm
  let vx: setvar x
  let cB: class B
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cV: class V
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  assume rrxval.r: |- H = ( RR^ ` I )
  assume rrxbase.b: |- B = ( Base ` H )

  disjoint f x
  disjoint B f
  disjoint B x
  disjoint I f
  disjoint I x
  disjoint V f
  disjoint V x
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint g x
  disjoint B g
  disjoint h x
  disjoint B h
  disjoint f i
  disjoint g i
  disjoint I g
  disjoint h i
  disjoint I h
  disjoint i x
  disjoint I i
  disjoint V g
  disjoint V h
  assert |- ( I e. V -> ( f e. B |-> ( sqrt ` ( RRfld gsum ( x e. I |-> ( ( f ` x ) ^ 2 ) ) ) ) ) = ( norm ` H ) )

  proof
    cI
    cV
    wcel
    #
    crefld
    cI
    cfrlm
    co
    #
    ctch
    cfv
    #
    cnm
    cfv
    #
    vf
    @1
    cbs
    cfv
    #
    vf
    cv
    #
    @5
    @1
    cip
    cfv
    #
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    cH
    cnm
    cfv
    vf
    cB
    crefld
    vx
    cI
    vx
    cv
    #
    @5
    cfv
    #
    c2
    cexp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    csqrt
    cfv
    #
    cmpt
    @0
    @1
    clmod
    wcel
    #
    @1
    cgrp
    wcel
    @3
    @9
    wceq
    crefld
    crg
    wcel
    #
    @0
    @16
    crefld
    csr
    wcel
    @17
    recrng
    crefld
    srngring
    ax-mp
    crefld
    @1
    cI
    cV
    @1
    eqid
    frlmlmod
    mpan
    @1
    lmodgrp
    vf
    @2
    @6
    @3
    @4
    @1
    @2
    eqid
    #
    @3
    eqid
    @4
    eqid
    #
    @6
    eqid
    #
    tchnmfval
    3syl
    @0
    cH
    @2
    cnm
    cH
    cI
    cV
    rrxval.r
    rrxval
    #
    fveq2d
    @0
    vf
    cB
    @15
    @4
    @8
    @0
    cH
    cbs
    cfv
    @2
    cbs
    cfv
    cB
    @4
    @0
    cH
    @2
    cbs
    @21
    fveq2d
    rrxbase.b
    @2
    @4
    @1
    @18
    @19
    tchbas
    3eqtr4g
    @0
    @5
    cB
    wcel
    #
    wa
    #
    @14
    @7
    csqrt
    @23
    @7
    @14
    @0
    @22
    @5
    cr
    cI
    cmap
    co
    #
    wcel
    #
    @7
    @14
    wceq
    @0
    cB
    @24
    @5
    @0
    cB
    @5
    cc0
    cfsupp
    wbr
    #
    vf
    @24
    crab
    @24
    cB
    vf
    cH
    cI
    cV
    rrxval.r
    rrxbase.b
    rrxbase
    @26
    vf
    @24
    ssrab2
    syl6eqss
    sselda
    @0
    @25
    wa
    #
    vh
    vg
    @5
    @5
    @24
    @24
    crefld
    vx
    cI
    @10
    vh
    cv
    #
    cfv
    #
    @10
    vg
    cv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @14
    @6
    cvv
    @0
    @6
    vh
    vg
    @24
    @24
    @34
    cmpt2
    #
    wceq
    @25
    @0
    cH
    cip
    cfv
    @2
    cip
    cfv
    #
    @35
    @6
    @0
    cH
    @2
    cip
    @21
    fveq2d
    vx
    cB
    vh
    vg
    cH
    cI
    cV
    rrxval.r
    rrxbase.b
    rrxip
    @6
    @36
    wceq
    @0
    @6
    @2
    @1
    @18
    @20
    tchip
    a1i
    3eqtr4rd
    adantr
    @27
    @28
    @5
    wceq
    #
    @30
    @5
    wceq
    #
    wa
    #
    wa
    #
    @33
    @13
    crefld
    cgsu
    @40
    vx
    cI
    @32
    @12
    @40
    @10
    cI
    wcel
    #
    wa
    #
    @32
    @11
    @11
    cmul
    co
    #
    @12
    @40
    @32
    @43
    wceq
    @41
    @40
    @29
    @11
    @31
    @11
    cmul
    @40
    @10
    @28
    @5
    @27
    @37
    @38
    simprl
    fveq1d
    @40
    @10
    @30
    @5
    @27
    @37
    @38
    simprr
    fveq1d
    oveq12d
    adantr
    @42
    @11
    @27
    @41
    @11
    cc
    wcel
    @39
    @27
    @41
    wa
    @11
    @27
    cI
    cr
    @10
    @5
    @25
    cI
    cr
    @5
    wf
    @0
    @5
    cr
    cI
    elmapi
    adantl
    ffvelrnda
    recnd
    adantlr
    sqvald
    eqtr4d
    mpteq2dva
    oveq2d
    @0
    @25
    simpr
    #
    @44
    @27
    crefld
    @13
    cgsu
    ovexd
    ovmpt2d
    syldan
    eqcomd
    fveq2d
    mpteq12dva
    3eqtr4rd
end
