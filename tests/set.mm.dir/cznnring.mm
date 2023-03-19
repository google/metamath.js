include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "wn.mm"
include "wnel.mm"
include "cgrp.mm"
include "cmgp.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cnx.mm"
include "cmulr.mm"
include "cmpt2.mm"
include "cop.mm"
include "csts.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "cznrnglem.mm"
include "mgpbas.mm"
include "fveq2i.mm"
include "cvv.mm"
include "czn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cbs.mm"
include "mpt2ex.mm"
include "mulrid.mm"
include "setsid.mm"
include "mp2an.mm"
include "mgpplusg.mm"
include "eqcomi.mm"
include "simpr.mm"
include "c1.mm"
include "chash.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "cle.mm"
include "eluz2.mm"
include "1lt2.mm"
include "wi.mm"
include "cr.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "zre.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "expcomd.mm"
include "3imp.mm"
include "mpi.mm"
include "sylbi.mm"
include "cn.mm"
include "eluz2nn.mm"
include "znhash.mm"
include "syl.mm"
include "breqtrrd.mm"
include "adantr.mm"
include "copisnmnd.mm"
include "df-nel.mm"
include "sylib.mm"
include "intn3an2d.mm"
include "isring.mm"
include "sylnibr.mm"
include "sylibr.mm"

theorem cznnring
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume cznrng.y: |- Y = ( Z/nZ ` N )
  assume cznrng.b: |- B = ( Base ` Y )
  assume cznrng.x: |- X = ( Y sSet <. ( .r ` ndx ) , ( x e. B , y e. B |-> C ) >. )
  assume cznrng.0: |- .0. = ( 0g ` Y )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint Y x
  disjoint Y y
  disjoint .0. x
  disjoint .0. y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint .0. a
  disjoint .0. b
  disjoint .0. c
  disjoint k x
  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ C e. B ) -> X e/ Ring )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cX
    crg
    wcel
    #
    wn
    cX
    crg
    wnel
    @2
    cX
    cgrp
    wcel
    #
    cX
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cX
    cplusg
    cfv
    #
    co
    cY
    cnx
    cmulr
    cfv
    vx
    vy
    cB
    cB
    cC
    cmpt2
    #
    cop
    csts
    co
    #
    cmulr
    cfv
    #
    co
    @7
    @8
    @13
    co
    @7
    @9
    @13
    co
    #
    @10
    co
    wceq
    @7
    @8
    @10
    co
    @9
    @13
    co
    @14
    @8
    @9
    @13
    co
    @10
    co
    wceq
    wa
    vc
    cB
    wral
    vb
    cB
    wral
    va
    cB
    wral
    #
    w3a
    @3
    @2
    @6
    @4
    @15
    @2
    @5
    cmnd
    wnel
    @6
    wn
    @2
    vx
    vy
    cB
    cC
    @5
    cB
    cX
    @5
    @5
    eqid
    #
    vx
    vy
    cB
    cC
    cN
    cX
    cY
    cznrng.y
    cznrng.b
    cznrng.x
    cznrnglem
    #
    mgpbas
    @11
    @5
    cplusg
    cfv
    @12
    @11
    @5
    cX
    @12
    cmgp
    cznrng.x
    fveq2i
    cY
    cvv
    wcel
    @11
    cvv
    wcel
    @11
    @13
    wceq
    cY
    cN
    czn
    cfv
    cvv
    cznrng.y
    cN
    czn
    fvex
    eqeltri
    vx
    vy
    cB
    cB
    cC
    cB
    cY
    cbs
    cfv
    cvv
    cznrng.b
    cY
    cbs
    fvex
    eqeltri
    #
    @18
    mpt2ex
    cvv
    @11
    cmulr
    cvv
    cY
    mulrid
    setsid
    mp2an
    mgpplusg
    eqcomi
    @0
    @1
    simpr
    @0
    c1
    cB
    chash
    cfv
    #
    clt
    wbr
    @1
    @0
    c1
    cN
    @19
    clt
    @0
    c2
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c2
    cN
    cle
    wbr
    #
    w3a
    #
    c1
    cN
    clt
    wbr
    #
    c2
    cN
    eluz2
    @23
    c1
    c2
    clt
    wbr
    #
    @24
    1lt2
    @20
    @21
    @22
    @25
    @24
    wi
    #
    @21
    @22
    @26
    wi
    wi
    @20
    @21
    @25
    @22
    @24
    @21
    c1
    cr
    wcel
    c2
    cr
    wcel
    #
    cN
    cr
    wcel
    @25
    @22
    wa
    @24
    wi
    @21
    1red
    @27
    @21
    2re
    a1i
    cN
    zre
    c1
    c2
    cN
    ltletr
    syl3anc
    expcomd
    a1i
    3imp
    mpi
    sylbi
    @0
    cN
    cn
    wcel
    @19
    cN
    wceq
    cN
    eluz2nn
    cB
    cN
    cY
    cznrng.y
    cznrng.b
    znhash
    syl
    breqtrrd
    adantr
    copisnmnd
    @5
    cmnd
    df-nel
    sylib
    intn3an2d
    va
    vb
    vc
    cB
    @10
    cX
    @13
    @5
    @17
    @16
    @10
    eqid
    @12
    cX
    cmulr
    cX
    @12
    cznrng.x
    eqcomi
    fveq2i
    isring
    sylnibr
    cX
    crg
    df-nel
    sylibr
end
