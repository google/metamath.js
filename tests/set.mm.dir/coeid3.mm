include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cuz.mm"
include "cc.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "coeid2.mm"
include "3adant2.mm"
include "wss.mm"
include "fzss2.mm"
include "3ad2ant2.mm"
include "cn0.mm"
include "elfznn0.mm"
include "wa.mm"
include "wf.mm"
include "coef3.mm"
include "3ad2ant1.mm"
include "ffvelrnda.mm"
include "expcl.mm"
include "3ad2antl3.mm"
include "mulcld.mm"
include "sylan2.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "simpl1.mm"
include "eldifi.mm"
include "elfzuz.mm"
include "syl.mm"
include "nn0uz.mm"
include "syl6eleqr.mm"
include "dgrub.mm"
include "3expia.mm"
include "syl2anc.mm"
include "cz.mm"
include "wb.mm"
include "simpl2.mm"
include "eluzel2.mm"
include "elfz5.mm"
include "sylibrd.mm"
include "necon1bd.mm"
include "mpd.mm"
include "oveq1d.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "fsumss.mm"

theorem coeid3
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let vm: setvar m
  let cB: class B
  assume dgrub.1: |- A = ( coeff ` F )
  assume dgrub.2: |- N = ( deg ` F )

  disjoint A k
  disjoint F k
  disjoint S k
  disjoint M k
  disjoint N k
  disjoint X k
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F a
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint k ph
  disjoint ph z
  disjoint a m
  disjoint S a
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint B k
  disjoint B z
  disjoint M y
  disjoint M z
  disjoint N a
  disjoint N n
  disjoint N z
  disjoint X z
  disjoint F z
  assert |- ( ( F e. ( Poly ` S ) /\ M e. ( ZZ>= ` N ) /\ X e. CC ) -> ( F ` X ) = sum_ k e. ( 0 ... M ) ( ( A ` k ) x. ( X ^ k ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cM
    cN
    cuz
    cfv
    wcel
    #
    cX
    cc
    wcel
    #
    w3a
    #
    cX
    cF
    cfv
    #
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    cX
    @6
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    cM
    cfz
    co
    #
    @9
    vk
    csu
    @0
    @2
    @4
    @10
    wceq
    @1
    cA
    cS
    vk
    cF
    cN
    cX
    dgrub.1
    dgrub.2
    coeid2
    3adant2
    @3
    @5
    @11
    @9
    vk
    @1
    @0
    @5
    @11
    wss
    @2
    cN
    cc0
    cM
    fzss2
    3ad2ant2
    @6
    @5
    wcel
    #
    @3
    @6
    cn0
    wcel
    #
    @9
    cc
    wcel
    @6
    cN
    elfznn0
    @3
    @13
    wa
    @7
    @8
    @3
    cn0
    cc
    @6
    cA
    @0
    @1
    cn0
    cc
    cA
    wf
    @2
    cA
    cS
    cF
    dgrub.1
    coef3
    3ad2ant1
    ffvelrnda
    @2
    @0
    @13
    @8
    cc
    wcel
    #
    @1
    cX
    @6
    expcl
    3ad2antl3
    #
    mulcld
    sylan2
    @3
    @6
    @11
    @5
    cdif
    wcel
    #
    wa
    #
    @9
    cc0
    @8
    cmul
    co
    cc0
    @17
    @7
    cc0
    @8
    cmul
    @17
    @12
    wn
    #
    @7
    cc0
    wceq
    @16
    @18
    @3
    @6
    @11
    @5
    eldifn
    adantl
    @17
    @12
    @7
    cc0
    @17
    @7
    cc0
    wne
    #
    @6
    cN
    cle
    wbr
    #
    @12
    @17
    @0
    @13
    @19
    @20
    wi
    @0
    @1
    @2
    @16
    simpl1
    @17
    @6
    cc0
    cuz
    cfv
    #
    cn0
    @16
    @6
    @21
    wcel
    #
    @3
    @16
    @6
    @11
    wcel
    #
    @22
    @6
    @11
    @5
    eldifi
    #
    @6
    cc0
    cM
    elfzuz
    syl
    adantl
    #
    nn0uz
    syl6eleqr
    @0
    @13
    @19
    @20
    cA
    cS
    cF
    @6
    cN
    dgrub.1
    dgrub.2
    dgrub
    3expia
    syl2anc
    @17
    @22
    cN
    cz
    wcel
    #
    @12
    @20
    wb
    @25
    @17
    @1
    @26
    @0
    @1
    @2
    @16
    simpl2
    cN
    cM
    eluzel2
    syl
    @6
    cc0
    cN
    elfz5
    syl2anc
    sylibrd
    necon1bd
    mpd
    oveq1d
    @17
    @8
    @16
    @3
    @13
    @14
    @16
    @23
    @13
    @24
    @6
    cM
    elfznn0
    syl
    @15
    sylan2
    mul02d
    eqtrd
    @3
    cc0
    cM
    fzfid
    fsumss
    eqtrd
end
