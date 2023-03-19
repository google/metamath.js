include "wss.mm"
include "cn.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "cif.mm"
include "cn0.mm"
include "nnnn0.mm"
include "0re.mm"
include "cr.mm"
include "1re.mm"
include "3nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "3re.mm"
include "3pos.mm"
include "recgt0ii.mm"
include "ltleii.mm"
include "expge0.mm"
include "mp3an1.mm"
include "sylancl.mm"
include "3ad2ant3.mm"
include "0le0.mm"
include "breq2.mm"
include "ifboth.mm"
include "wceq.mm"
include "sstr.mm"
include "rpnnen2lem1.mm"
include "stoic3.mm"
include "breqtrrd.mm"
include "wi.mm"
include "reexpcl.mm"
include "sylancr.mm"
include "0red.mm"
include "simp1.mm"
include "sseld.mm"
include "ifle.mm"
include "syl31anc.mm"
include "3adant1.mm"
include "3brtr4d.mm"
include "jca.mm"

theorem rpnnen2lem4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint N n
  assert |- ( ( A C_ B /\ B C_ NN /\ k e. NN ) -> ( 0 <_ ( ( F ` A ) ` k ) /\ ( ( F ` A ) ` k ) <_ ( ( F ` B ) ` k ) ) )

  proof
    cA
    cB
    wss
    #
    cB
    cn
    wss
    #
    vk
    cv
    #
    cn
    wcel
    #
    w3a
    #
    cc0
    @2
    cA
    cF
    cfv
    cfv
    #
    cle
    wbr
    @5
    @2
    cB
    cF
    cfv
    cfv
    #
    cle
    wbr
    @4
    cc0
    @2
    cA
    wcel
    #
    c1
    c3
    cdiv
    co
    #
    @2
    cexp
    co
    #
    cc0
    cif
    #
    @5
    cle
    @4
    cc0
    @9
    cle
    wbr
    #
    cc0
    cc0
    cle
    wbr
    #
    cc0
    @10
    cle
    wbr
    #
    @3
    @0
    @11
    @1
    @3
    @2
    cn0
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    @11
    @2
    nnnn0
    #
    cc0
    @8
    0re
    c1
    cr
    wcel
    c3
    cn
    wcel
    @8
    cr
    wcel
    #
    1re
    3nn
    c1
    c3
    nndivre
    mp2an
    #
    c3
    3re
    3pos
    recgt0ii
    ltleii
    @17
    @14
    @15
    @11
    @18
    @8
    @2
    expge0
    mp3an1
    sylancl
    3ad2ant3
    #
    0le0
    @7
    @11
    @12
    @13
    @9
    cc0
    @9
    @10
    cc0
    cle
    breq2
    cc0
    @10
    cc0
    cle
    breq2
    ifboth
    sylancl
    @0
    @1
    cA
    cn
    wss
    @3
    @5
    @10
    wceq
    cA
    cB
    cn
    sstr
    vx
    cA
    vn
    cF
    @2
    rpnnen2.1
    rpnnen2lem1
    stoic3
    #
    breqtrrd
    @4
    @10
    @2
    cB
    wcel
    #
    @9
    cc0
    cif
    #
    @5
    @6
    cle
    @4
    @9
    cr
    wcel
    #
    cc0
    cr
    wcel
    @11
    @7
    @21
    wi
    @10
    @22
    cle
    wbr
    @3
    @0
    @23
    @1
    @3
    @17
    @14
    @23
    @18
    @16
    @8
    @2
    reexpcl
    sylancr
    3ad2ant3
    @4
    0red
    @19
    @4
    cA
    cB
    @2
    @0
    @1
    @3
    simp1
    sseld
    @7
    @21
    @9
    cc0
    ifle
    syl31anc
    @20
    @1
    @3
    @6
    @22
    wceq
    @0
    vx
    cB
    vn
    cF
    @2
    rpnnen2.1
    rpnnen2lem1
    3adant1
    3brtr4d
    jca
end
