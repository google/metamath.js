include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "cmin.mm"
include "wceq.mm"
include "simp1.mm"
include "simpl.mm"
include "eluznn0.mm"
include "eluzle.mm"
include "adantl.mm"
include "3jca.mm"
include "3ad2ant2.mm"
include "elfz2nn0.mm"
include "sylibr.mm"
include "lencl.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "swrdlen.mm"
include "syl3anc.mm"

theorem swrdlen2
  let cS: class S
  let cF: class F
  let cL: class L
  let cV: class V


  assert |- ( ( S e. Word V /\ ( F e. NN0 /\ L e. ( ZZ>= ` F ) ) /\ L <_ ( # ` S ) ) -> ( # ` ( S substr <. F , L >. ) ) = ( L - F ) )

  proof
    cS
    cV
    cword
    wcel
    #
    cF
    cn0
    wcel
    #
    cL
    cF
    cuz
    cfv
    wcel
    #
    wa
    #
    cL
    cS
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    @0
    cF
    cc0
    cL
    cfz
    co
    wcel
    #
    cL
    cc0
    @4
    cfz
    co
    wcel
    #
    cS
    cF
    cL
    cop
    csubstr
    co
    chash
    cfv
    cL
    cF
    cmin
    co
    wceq
    @0
    @3
    @5
    simp1
    @6
    @1
    cL
    cn0
    wcel
    #
    cF
    cL
    cle
    wbr
    #
    w3a
    #
    @7
    @3
    @0
    @11
    @5
    @3
    @1
    @9
    @10
    @1
    @2
    simpl
    cL
    cF
    eluznn0
    #
    @2
    @10
    @1
    cF
    cL
    eluzle
    adantl
    3jca
    3ad2ant2
    cF
    cL
    elfz2nn0
    sylibr
    @6
    @9
    @4
    cn0
    wcel
    #
    @5
    w3a
    @8
    @6
    @9
    @13
    @5
    @3
    @0
    @9
    @5
    @12
    3ad2ant2
    @0
    @3
    @13
    @5
    cV
    cS
    lencl
    3ad2ant1
    @0
    @3
    @5
    simp3
    3jca
    cL
    @4
    elfz2nn0
    sylibr
    cV
    cS
    cF
    cL
    swrdlen
    syl3anc
end
