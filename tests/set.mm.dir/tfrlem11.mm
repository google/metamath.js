include "crecs.mm"
include "cdm.mm"
include "csuc.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "con0.mm"
include "cfv.mm"
include "cres.mm"
include "elsuci.mm"
include "wi.mm"
include "wfun.mm"
include "wa.mm"
include "wfn.mm"
include "tfrlem10.mm"
include "fnfun.mm"
include "syl.mm"
include "wss.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "tfrlem9.mm"
include "funssfv.mm"
include "3expa.mm"
include "adantrl.mm"
include "onelss.mm"
include "imp.mm"
include "fun2ssres.mm"
include "fveq2d.mm"
include "sylan2.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "mpanl2.mm"
include "sylan.mm"
include "exp32.mm"
include "pm2.43i.mm"
include "pm2.43d.mm"
include "opex.mm"
include "snid.mm"
include "opeq1.mm"
include "adantl.mm"
include "eqimss.mm"
include "mp3an2.mm"
include "syl2an.mm"
include "reseq2.mm"
include "wrel.mm"
include "tfrlem6.mm"
include "resdm.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "syl5eleq.mm"
include "elun2.mm"
include "syl6eleqr.mm"
include "wb.mm"
include "adantr.mm"
include "simpr.mm"
include "sucidg.mm"
include "eqeltrd.mm"
include "fnopfvb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ex.mm"
include "jaod.mm"
include "syl5.mm"

theorem tfrlem11
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }
  assume tfrlem.3: |- C = ( recs ( F ) u. { <. dom recs ( F ) , ( F ` recs ( F ) ) >. } )

  disjoint f x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C z
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint A g
  disjoint A h
  disjoint A z
  assert |- ( dom recs ( F ) e. On -> ( B e. suc dom recs ( F ) -> ( C ` B ) = ( F ` ( C |` B ) ) ) )

  proof
    cB
    cF
    crecs
    #
    cdm
    #
    csuc
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cB
    @1
    wceq
    #
    wo
    @1
    con0
    wcel
    #
    cB
    cC
    cfv
    #
    cC
    cB
    cres
    #
    cF
    cfv
    #
    wceq
    #
    cB
    @1
    elsuci
    @6
    @4
    @10
    @5
    @6
    @4
    @10
    @6
    @4
    @4
    @10
    wi
    #
    wi
    @6
    @6
    @4
    @11
    @6
    cC
    wfun
    #
    @6
    @4
    wa
    #
    @11
    @6
    cC
    @2
    wfn
    #
    @12
    vx
    vy
    cA
    cC
    vf
    cF
    tfrlem.1
    tfrlem.3
    tfrlem10
    #
    @2
    cC
    fnfun
    syl
    #
    @12
    @0
    cC
    wss
    #
    @13
    @11
    @0
    @0
    @1
    @0
    cF
    cfv
    #
    cop
    #
    csn
    #
    cun
    #
    cC
    @0
    @20
    ssun1
    tfrlem.3
    sseqtr4i
    #
    @4
    @10
    @12
    @17
    wa
    #
    @13
    wa
    #
    cB
    @0
    cfv
    #
    @0
    cB
    cres
    #
    cF
    cfv
    #
    wceq
    vx
    vy
    cA
    cB
    vf
    cF
    tfrlem.1
    tfrlem9
    @24
    @7
    @25
    @9
    @27
    @23
    @4
    @7
    @25
    wceq
    #
    @6
    @12
    @17
    @4
    @28
    cB
    cC
    @0
    funssfv
    3expa
    adantrl
    @13
    @23
    cB
    @1
    wss
    #
    @9
    @27
    wceq
    @6
    @4
    @29
    @1
    cB
    onelss
    imp
    @23
    @29
    wa
    @8
    @26
    cF
    @12
    @17
    @29
    @8
    @26
    wceq
    #
    cB
    cC
    @0
    fun2ssres
    #
    3expa
    fveq2d
    sylan2
    eqeq12d
    syl5ibr
    mpanl2
    sylan
    exp32
    pm2.43i
    pm2.43d
    @6
    @5
    @10
    @6
    @5
    wa
    #
    @10
    cB
    @9
    cop
    #
    cC
    wcel
    #
    @32
    @33
    @21
    cC
    @32
    @33
    @20
    wcel
    @33
    @21
    wcel
    @32
    @33
    @33
    csn
    @20
    @33
    cB
    @9
    opex
    snid
    @32
    @33
    @19
    @32
    @33
    @1
    @9
    cop
    #
    @19
    @5
    @33
    @35
    wceq
    @6
    cB
    @1
    @9
    opeq1
    adantl
    @32
    @9
    @18
    @1
    @32
    @8
    @0
    cF
    @32
    @8
    @26
    @0
    @6
    @12
    @29
    @30
    @5
    @16
    cB
    @1
    eqimss
    @12
    @17
    @29
    @30
    @22
    @31
    mp3an2
    syl2an
    @5
    @26
    @0
    wceq
    @6
    @5
    @26
    @0
    @1
    cres
    #
    @0
    cB
    @1
    @0
    reseq2
    @0
    wrel
    @36
    @0
    wceq
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem6
    @0
    resdm
    ax-mp
    syl6eq
    adantl
    eqtrd
    fveq2d
    opeq2d
    eqtrd
    sneqd
    syl5eleq
    @33
    @20
    @0
    elun2
    syl
    tfrlem.3
    syl6eleqr
    @32
    @14
    @3
    @10
    @34
    wb
    @6
    @14
    @5
    @15
    adantr
    @32
    cB
    @1
    @2
    @6
    @5
    simpr
    @6
    @1
    @2
    wcel
    @5
    @1
    con0
    sucidg
    adantr
    eqeltrd
    @2
    cB
    @9
    cC
    fnopfvb
    syl2anc
    mpbird
    ex
    jaod
    syl5
end
