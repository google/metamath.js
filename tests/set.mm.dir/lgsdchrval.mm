include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cz.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "clgs.mm"
include "co.mm"
include "wrex.mm"
include "cio.mm"
include "cn0.mm"
include "wfo.mm"
include "wf.mm"
include "nnnn0.mm"
include "adantr.mm"
include "znzrhfo.mm"
include "fof.mm"
include "3syl.mm"
include "ffvelrnda.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "iotabidv.mm"
include "iotaex.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "cvv.mm"
include "ovex.mm"
include "wb.mm"
include "wi.mm"
include "cmo.mm"
include "cmin.mm"
include "simprr.mm"
include "simplll.mm"
include "simplr.mm"
include "simprl.mm"
include "zndvds.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "moddvds.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "simpllr.mm"
include "lgsmod.mm"
include "3eqtr3d.mm"
include "eqeq2d.mm"
include "biimprd.mm"
include "anassrs.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "biantrurd.mm"
include "oveq1.mm"
include "bitr3d.mm"
include "rspcev.mm"
include "ex.mm"
include "adantl.mm"
include "impbid.mm"
include "iota5.mm"
include "mpan2.mm"
include "eqtrd.mm"

theorem lgsdchrval
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let vh: setvar h
  let vm: setvar m
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lgsdchr.g: |- G = ( DChr ` N )
  assume lgsdchr.z: |- Z = ( Z/nZ ` N )
  assume lgsdchr.d: |- D = ( Base ` G )
  assume lgsdchr.b: |- B = ( Base ` Z )
  assume lgsdchr.l: |- L = ( ZRHom ` Z )
  assume lgsdchr.x: |- X = ( y e. B |-> ( iota h E. m e. ZZ ( y = ( L ` m ) /\ h = ( m /L N ) ) ) )

  disjoint B y
  disjoint h m
  disjoint h y
  disjoint L h
  disjoint m y
  disjoint L m
  disjoint L y
  disjoint N h
  disjoint N m
  disjoint N y
  disjoint X y
  disjoint A h
  disjoint A m
  disjoint A y
  disjoint Z y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint x y
  disjoint B x
  disjoint a h
  disjoint a m
  disjoint L a
  disjoint b h
  disjoint b m
  disjoint L b
  disjoint N a
  disjoint N b
  disjoint h x
  disjoint m x
  disjoint N x
  disjoint X a
  disjoint X b
  disjoint X x
  disjoint Z a
  disjoint Z b
  disjoint Z x
  assert |- ( ( ( N e. NN /\ -. 2 || N ) /\ A e. ZZ ) -> ( X ` ( L ` A ) ) = ( A /L N ) )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    wa
    #
    cA
    cz
    wcel
    #
    wa
    #
    cA
    cL
    cfv
    #
    cX
    cfv
    #
    @5
    vm
    cv
    #
    cL
    cfv
    #
    wceq
    #
    vh
    cv
    #
    @7
    cN
    clgs
    co
    #
    wceq
    #
    wa
    #
    vm
    cz
    wrex
    #
    vh
    cio
    #
    cA
    cN
    clgs
    co
    #
    @4
    @5
    cB
    wcel
    @6
    @15
    wceq
    @2
    cz
    cB
    cA
    cL
    @2
    cN
    cn0
    wcel
    #
    cz
    cB
    cL
    wfo
    cz
    cB
    cL
    wf
    @0
    @17
    @1
    cN
    nnnn0
    #
    adantr
    cB
    cL
    cN
    cZ
    lgsdchr.z
    lgsdchr.b
    lgsdchr.l
    znzrhfo
    cz
    cB
    cL
    fof
    3syl
    ffvelrnda
    vy
    @5
    vy
    cv
    #
    @8
    wceq
    #
    @12
    wa
    #
    vm
    cz
    wrex
    #
    vh
    cio
    @15
    cB
    cX
    @19
    @5
    wceq
    #
    @22
    @14
    vh
    @23
    @21
    @13
    vm
    cz
    @23
    @20
    @9
    @12
    @19
    @5
    @8
    eqeq1
    anbi1d
    rexbidv
    iotabidv
    lgsdchr.x
    @22
    vh
    iotaex
    fvmpt3i
    syl
    @4
    @16
    cvv
    wcel
    #
    @15
    @16
    wceq
    cA
    cN
    clgs
    ovex
    @4
    @14
    vh
    @16
    cvv
    @4
    @14
    @10
    @16
    wceq
    #
    wb
    @24
    @4
    @14
    @25
    @4
    @13
    @25
    vm
    cz
    @4
    @7
    cz
    wcel
    #
    wa
    @9
    @12
    @25
    @4
    @26
    @9
    @12
    @25
    wi
    @4
    @26
    @9
    wa
    #
    wa
    #
    @25
    @12
    @28
    @16
    @11
    @10
    @28
    cA
    cN
    cmo
    co
    #
    cN
    clgs
    co
    #
    @7
    cN
    cmo
    co
    #
    cN
    clgs
    co
    #
    @16
    @11
    @28
    @29
    @31
    cN
    clgs
    @28
    @29
    @31
    wceq
    #
    cN
    cA
    @7
    cmin
    co
    cdvds
    wbr
    #
    @28
    @9
    @34
    @4
    @26
    @9
    simprr
    @28
    @17
    @3
    @26
    @9
    @34
    wb
    @28
    @0
    @17
    @0
    @1
    @3
    @27
    simplll
    #
    @18
    syl
    @2
    @3
    @27
    simplr
    #
    @4
    @26
    @9
    simprl
    #
    cA
    @7
    cL
    cN
    cZ
    lgsdchr.z
    lgsdchr.l
    zndvds
    syl3anc
    mpbid
    @28
    @0
    @3
    @26
    @33
    @34
    wb
    @35
    @36
    @37
    cA
    @7
    cN
    moddvds
    syl3anc
    mpbird
    oveq1d
    @28
    @3
    @0
    @1
    @30
    @16
    wceq
    @36
    @35
    @0
    @1
    @3
    @27
    simpllr
    #
    cA
    cN
    lgsmod
    syl3anc
    @28
    @26
    @0
    @1
    @32
    @11
    wceq
    @37
    @35
    @38
    @7
    cN
    lgsmod
    syl3anc
    3eqtr3d
    eqeq2d
    biimprd
    anassrs
    expimpd
    rexlimdva
    @3
    @25
    @14
    wi
    @2
    @3
    @25
    @14
    @13
    @25
    vm
    cA
    cz
    @7
    cA
    wceq
    #
    @12
    @13
    @25
    @39
    @9
    @12
    @39
    @8
    @5
    @7
    cA
    cL
    fveq2
    eqcomd
    biantrurd
    @39
    @11
    @16
    @10
    @7
    cA
    cN
    clgs
    oveq1
    eqeq2d
    bitr3d
    rspcev
    ex
    adantl
    impbid
    adantr
    iota5
    mpan2
    eqtrd
end
