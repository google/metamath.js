include "cn.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cfv.mm"
include "c1.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "nnuz.mm"
include "1nn.mm"
include "a1i.mm"
include "cr.mm"
include "cv.mm"
include "wf.mm"
include "ssid.mm"
include "rpnnen2lem2.mm"
include "mp1i.mm"
include "ffvelrnda.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "wbr.mm"
include "rpnnen2lem3.mm"
include "seqex.mm"
include "ovex.mm"
include "breldm.mm"
include "cuz.mm"
include "cc0.mm"
include "cle.mm"
include "elnnuz.mm"
include "rpnnen2lem4.mm"
include "mp3an2.mm"
include "sylan2br.mm"
include "simpld.mm"
include "simprd.mm"
include "cvgcmp.mm"
include "adantr.mm"
include "simpr.mm"
include "adantlr.mm"
include "recnd.mm"
include "iserex.mm"
include "mpbid.mm"

theorem rpnnen2lem5
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint M n
  disjoint M x
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint M k
  disjoint N n
  assert |- ( ( A C_ NN /\ M e. NN ) -> seq M ( + , ( F ` A ) ) e. dom ~~> )

  proof
    cA
    cn
    wss
    #
    cM
    cn
    wcel
    #
    wa
    #
    caddc
    cA
    cF
    cfv
    #
    c1
    cseq
    cli
    cdm
    #
    wcel
    #
    caddc
    @3
    cM
    cseq
    @4
    wcel
    @0
    @5
    @1
    @0
    vk
    cn
    cF
    cfv
    #
    @3
    c1
    c1
    cn
    nnuz
    c1
    cn
    wcel
    @0
    1nn
    a1i
    @0
    cn
    cr
    vk
    cv
    #
    @6
    cn
    cn
    wss
    #
    cn
    cr
    @6
    wf
    @0
    cn
    ssid
    #
    vx
    cn
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    mp1i
    ffvelrnda
    @0
    cn
    cr
    @7
    @3
    vx
    cA
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    ffvelrnda
    #
    caddc
    @6
    c1
    cseq
    #
    c1
    c2
    cdiv
    co
    #
    cli
    wbr
    @11
    @4
    wcel
    @0
    vx
    vn
    cF
    rpnnen2.1
    rpnnen2lem3
    @11
    @12
    cli
    caddc
    @6
    c1
    seqex
    c1
    c2
    cdiv
    ovex
    breldm
    mp1i
    @0
    @7
    c1
    cuz
    cfv
    wcel
    #
    wa
    #
    cc0
    @7
    @3
    cfv
    #
    cle
    wbr
    #
    @15
    @7
    @6
    cfv
    cle
    wbr
    #
    @13
    @0
    @7
    cn
    wcel
    #
    @16
    @17
    wa
    #
    @7
    elnnuz
    @0
    @8
    @18
    @19
    @9
    vx
    cA
    cn
    vk
    vn
    cF
    rpnnen2.1
    rpnnen2lem4
    mp3an2
    sylan2br
    #
    simpld
    @14
    @16
    @17
    @20
    simprd
    cvgcmp
    adantr
    @2
    vk
    @3
    c1
    cM
    cn
    nnuz
    @0
    @1
    simpr
    @2
    @18
    wa
    @15
    @0
    @18
    @15
    cr
    wcel
    @1
    @10
    adantlr
    recnd
    iserex
    mpbid
end
