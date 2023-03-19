include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "id.mm"
include "imp.mm"
include "adantll.mm"
include "0le0.mm"
include "cn0v.mm"
include "cnv.mm"
include "cba.mm"
include "eqid.mm"
include "lno0.mm"
include "mp3an12.mm"
include "nvz0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "adantr.mm"
include "oveq2i.mm"
include "recn.mm"
include "mul01d.mm"
include "syl5eq.mm"
include "ad2antrl.mm"
include "mpbiri.mm"
include "pm2.61ne.mm"
include "ex.mm"
include "ralimdv.mm"
include "3impia.mm"
include "wf.mm"
include "lnof.mm"
include "nmoub2i.mm"
include "syl3an1.mm"
include "syld3an3.mm"

theorem nmlnoubi
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cU: class U
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume nmlnoubi.1: |- X = ( BaseSet ` U )
  assume nmlnoubi.z: |- Z = ( 0vec ` U )
  assume nmlnoubi.k: |- K = ( normCV ` U )
  assume nmlnoubi.m: |- M = ( normCV ` W )
  assume nmlnoubi.3: |- N = ( U normOpOLD W )
  assume nmlnoubi.7: |- L = ( U LnOp W )
  assume nmlnoubi.u: |- U e. NrmCVec
  assume nmlnoubi.w: |- W e. NrmCVec

  disjoint A x
  disjoint K x
  disjoint L x
  disjoint M x
  disjoint T x
  disjoint U x
  disjoint W x
  disjoint X x
  assert |- ( ( T e. L /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. X ( x =/= Z -> ( M ` ( T ` x ) ) <_ ( A x. ( K ` x ) ) ) ) -> ( N ` T ) <_ A )

  proof
    cT
    cL
    wcel
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    vx
    cv
    #
    cZ
    wne
    #
    @4
    cT
    cfv
    #
    cM
    cfv
    #
    cA
    @4
    cK
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    vx
    cX
    wral
    #
    @10
    vx
    cX
    wral
    #
    cT
    cN
    cfv
    cA
    cle
    wbr
    #
    @0
    @3
    @12
    @13
    @0
    @3
    wa
    #
    @11
    @10
    vx
    cX
    @15
    @11
    @10
    @15
    @11
    wa
    @10
    cZ
    cT
    cfv
    #
    cM
    cfv
    #
    cA
    cZ
    cK
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @4
    cZ
    @4
    cZ
    wceq
    #
    @7
    @17
    @9
    @19
    cle
    @21
    @6
    @16
    cM
    @4
    cZ
    cT
    fveq2
    fveq2d
    @21
    @8
    @18
    cA
    cmul
    @4
    cZ
    cK
    fveq2
    oveq2d
    breq12d
    @11
    @5
    @10
    @15
    @11
    @5
    @10
    @11
    id
    imp
    adantll
    @15
    @20
    @11
    @15
    @20
    cc0
    cc0
    cle
    wbr
    0le0
    @15
    @17
    cc0
    @19
    cc0
    cle
    @0
    @17
    cc0
    wceq
    @3
    @0
    @17
    cW
    cn0v
    cfv
    #
    cM
    cfv
    #
    cc0
    @0
    @16
    @22
    cM
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    @0
    @16
    @22
    wceq
    nmlnoubi.u
    nmlnoubi.w
    cZ
    cT
    cU
    cL
    cW
    cX
    cW
    cba
    cfv
    #
    @22
    nmlnoubi.1
    @26
    eqid
    #
    nmlnoubi.z
    @22
    eqid
    #
    nmlnoubi.7
    lno0
    mp3an12
    fveq2d
    @25
    @23
    cc0
    wceq
    nmlnoubi.w
    cW
    cM
    @22
    @28
    nmlnoubi.m
    nvz0
    ax-mp
    syl6eq
    adantr
    @1
    @19
    cc0
    wceq
    @0
    @2
    @1
    @19
    cA
    cc0
    cmul
    co
    cc0
    @18
    cc0
    cA
    cmul
    @24
    @18
    cc0
    wceq
    nmlnoubi.u
    cU
    cK
    cZ
    nmlnoubi.z
    nmlnoubi.k
    nvz0
    ax-mp
    oveq2i
    @1
    cA
    cA
    recn
    mul01d
    syl5eq
    ad2antrl
    breq12d
    mpbiri
    adantr
    pm2.61ne
    ex
    ralimdv
    3impia
    @0
    cX
    @26
    cT
    wf
    #
    @3
    @13
    @14
    @24
    @25
    @0
    @29
    nmlnoubi.u
    nmlnoubi.w
    cT
    cU
    cL
    cW
    cX
    @26
    nmlnoubi.1
    @27
    nmlnoubi.7
    lnof
    mp3an12
    vx
    cA
    cT
    cU
    cK
    cM
    cN
    cW
    cX
    @26
    nmlnoubi.1
    @27
    nmlnoubi.k
    nmlnoubi.m
    nmlnoubi.3
    nmlnoubi.u
    nmlnoubi.w
    nmoub2i
    syl3an1
    syld3an3
end
