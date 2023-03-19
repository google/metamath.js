include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmt.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wral.mm"
include "eqid.mm"
include "isngp2.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "cr.mm"
include "wf.mm"
include "cme.mm"
include "msmet2.mm"
include "nmf2.mm"
include "sylan2.mm"
include "grpsubf.mm"
include "adantr.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "adantl.mm"
include "metf.mm"
include "3syl.mm"
include "eqfnov2.mm"
include "cop.mm"
include "opelxpi.mm"
include "fvco3.mm"
include "syl2an.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "ovres.mm"
include "eqeq12d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "2ralbidva.mm"
include "bitrd.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem isngp3
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let vg: setvar g
  assume isngp.n: |- N = ( norm ` G )
  assume isngp.z: |- .- = ( -g ` G )
  assume isngp.d: |- D = ( dist ` G )
  assume isngp2.x: |- X = ( Base ` G )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint G x
  disjoint G y
  disjoint .- x
  disjoint .- y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint X y
  disjoint g x
  disjoint g y
  disjoint D g
  disjoint G g
  disjoint .- g
  disjoint N g
  assert |- ( G e. NrmGrp <-> ( G e. Grp /\ G e. MetSp /\ A. x e. X A. y e. X ( x D y ) = ( N ` ( x .- y ) ) ) )

  proof
    cG
    cngp
    wcel
    cG
    cgrp
    wcel
    #
    cG
    cmt
    wcel
    #
    cN
    c.mi
    ccom
    #
    cD
    cX
    cX
    cxp
    #
    cres
    #
    wceq
    #
    w3a
    #
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    @7
    @8
    c.mi
    co
    #
    cN
    cfv
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    w3a
    #
    cD
    @4
    cG
    c.mi
    cN
    cX
    isngp.n
    isngp.z
    isngp.d
    isngp2.x
    @4
    eqid
    #
    isngp2
    @0
    @1
    wa
    #
    @5
    wa
    @16
    @13
    wa
    @6
    @14
    @16
    @5
    @13
    @16
    @5
    @7
    @8
    @2
    co
    #
    @7
    @8
    @4
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @13
    @16
    @2
    @3
    wfn
    #
    @4
    @3
    wfn
    #
    @5
    @20
    wb
    @16
    @3
    cr
    @2
    wf
    #
    @21
    @16
    cX
    cr
    cN
    wf
    #
    @3
    cX
    c.mi
    wf
    #
    @23
    @1
    @0
    @4
    cX
    cme
    cfv
    wcel
    #
    @24
    cD
    cG
    cX
    isngp2.x
    isngp.d
    msmet2
    #
    cD
    @4
    cN
    cG
    cX
    isngp.n
    isngp2.x
    isngp.d
    @15
    nmf2
    sylan2
    @0
    @25
    @1
    cX
    cG
    c.mi
    isngp2.x
    isngp.z
    grpsubf
    adantr
    #
    @3
    cX
    cr
    cN
    c.mi
    fco
    syl2anc
    @3
    cr
    @2
    ffn
    syl
    @16
    @26
    @3
    cr
    @4
    wf
    @22
    @1
    @26
    @0
    @27
    adantl
    @4
    cX
    metf
    @3
    cr
    @4
    ffn
    3syl
    vx
    vy
    cX
    cX
    @2
    @4
    eqfnov2
    syl2anc
    @16
    @19
    @12
    vx
    vy
    cX
    cX
    @16
    @7
    cX
    wcel
    @8
    cX
    wcel
    wa
    #
    wa
    #
    @19
    @11
    @9
    wceq
    @12
    @30
    @17
    @11
    @18
    @9
    @30
    @7
    @8
    cop
    #
    @2
    cfv
    #
    @31
    c.mi
    cfv
    #
    cN
    cfv
    #
    @17
    @11
    @16
    @25
    @31
    @3
    wcel
    @32
    @34
    wceq
    @29
    @28
    @7
    @8
    cX
    cX
    opelxpi
    @3
    cX
    @31
    cN
    c.mi
    fvco3
    syl2an
    @7
    @8
    @2
    df-ov
    @10
    @33
    cN
    @7
    @8
    c.mi
    df-ov
    fveq2i
    3eqtr4g
    @29
    @18
    @9
    wceq
    @16
    @7
    @8
    cX
    cX
    cD
    ovres
    adantl
    eqeq12d
    @11
    @9
    eqcom
    syl6bb
    2ralbidva
    bitrd
    pm5.32i
    @0
    @1
    @5
    df-3an
    @0
    @1
    @13
    df-3an
    3bitr4i
    bitri
end
