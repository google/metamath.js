include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "cnv.mm"
include "bloln.mm"
include "mp3an12.mm"
include "cnmoo.mm"
include "cba.mm"
include "eqid.mm"
include "nmblore.mm"
include "nmblolbi.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "jca.mm"
include "w3a.mm"
include "cpnf.mm"
include "clt.mm"
include "simp1.mm"
include "wf.mm"
include "lnof.mm"
include "cabs.mm"
include "cxr.mm"
include "nmoxr.mm"
include "3ad2ant1.mm"
include "recn.mm"
include "abscld.mm"
include "rexrd.mm"
include "3ad2ant2.mm"
include "pnfxr.mm"
include "a1i.mm"
include "nmoub3i.mm"
include "ltpnf.mm"
include "syl.mm"
include "xrlelttrd.mm"
include "syl3an1.mm"
include "wb.mm"
include "isblo.mm"
include "mp2an.mm"
include "sylanbrc.mm"
include "rexlimdv3a.mm"
include "imp.mm"
include "impbii.mm"

theorem isblo3i
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cA: class A
  assume isblo3i.1: |- X = ( BaseSet ` U )
  assume isblo3i.m: |- M = ( normCV ` U )
  assume isblo3i.n: |- N = ( normCV ` W )
  assume isblo3i.4: |- L = ( U LnOp W )
  assume isblo3i.5: |- B = ( U BLnOp W )
  assume isblo3i.u: |- U e. NrmCVec
  assume isblo3i.w: |- W e. NrmCVec

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint L x
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  assert |- ( T e. B <-> ( T e. L /\ E. x e. RR A. y e. X ( N ` ( T ` y ) ) <_ ( x x. ( M ` y ) ) ) )

  proof
    cT
    cB
    wcel
    #
    cT
    cL
    wcel
    #
    vy
    cv
    #
    cT
    cfv
    cN
    cfv
    #
    vx
    cv
    #
    @2
    cM
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cr
    wrex
    #
    wa
    @0
    @1
    @9
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    @0
    @1
    isblo3i.u
    isblo3i.w
    cB
    cT
    cU
    cL
    cW
    isblo3i.4
    isblo3i.5
    bloln
    mp3an12
    @0
    cT
    cU
    cW
    cnmoo
    co
    #
    cfv
    #
    cr
    wcel
    #
    @3
    @13
    @5
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    @9
    @10
    @11
    @0
    @14
    isblo3i.u
    isblo3i.w
    cB
    cT
    cU
    @12
    cW
    cX
    cW
    cba
    cfv
    #
    isblo3i.1
    @18
    eqid
    #
    @12
    eqid
    #
    isblo3i.5
    nmblore
    mp3an12
    @0
    @16
    vy
    cX
    @2
    cB
    cT
    cU
    cM
    cN
    @12
    cW
    cX
    isblo3i.1
    isblo3i.m
    isblo3i.n
    @20
    isblo3i.5
    isblo3i.u
    isblo3i.w
    nmblolbi
    ralrimiva
    @8
    @17
    vx
    @13
    cr
    @4
    @13
    wceq
    #
    @7
    @16
    vy
    cX
    @21
    @6
    @15
    @3
    cle
    @4
    @13
    @5
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    syl2anc
    jca
    @1
    @9
    @0
    @1
    @8
    @0
    vx
    cr
    @1
    @4
    cr
    wcel
    #
    @8
    w3a
    @1
    @13
    cpnf
    clt
    wbr
    #
    @0
    @1
    @22
    @8
    simp1
    @1
    cX
    @18
    cT
    wf
    #
    @22
    @8
    @23
    @10
    @11
    @1
    @24
    isblo3i.u
    isblo3i.w
    cT
    cU
    cL
    cW
    cX
    @18
    isblo3i.1
    @19
    isblo3i.4
    lnof
    mp3an12
    @24
    @22
    @8
    w3a
    #
    @13
    @4
    cabs
    cfv
    #
    cpnf
    @24
    @22
    @13
    cxr
    wcel
    #
    @8
    @10
    @11
    @24
    @27
    isblo3i.u
    isblo3i.w
    cT
    cU
    @12
    cW
    cX
    @18
    isblo3i.1
    @19
    @20
    nmoxr
    mp3an12
    3ad2ant1
    @22
    @24
    @26
    cxr
    wcel
    @8
    @22
    @26
    @22
    @4
    @4
    recn
    abscld
    #
    rexrd
    3ad2ant2
    cpnf
    cxr
    wcel
    @25
    pnfxr
    a1i
    vy
    @4
    cT
    cU
    cM
    cN
    @12
    cW
    cX
    @18
    isblo3i.1
    @19
    isblo3i.m
    isblo3i.n
    @20
    isblo3i.u
    isblo3i.w
    nmoub3i
    @22
    @24
    @26
    cpnf
    clt
    wbr
    #
    @8
    @22
    @26
    cr
    wcel
    @29
    @28
    @26
    ltpnf
    syl
    3ad2ant2
    xrlelttrd
    syl3an1
    @10
    @11
    @0
    @1
    @23
    wa
    wb
    isblo3i.u
    isblo3i.w
    cB
    cT
    cU
    cL
    @12
    cW
    @20
    isblo3i.4
    isblo3i.5
    isblo
    mp2an
    sylanbrc
    rexlimdv3a
    imp
    impbii
end
