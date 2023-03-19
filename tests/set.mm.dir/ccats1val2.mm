include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "caddc.mm"
include "cfzo.mm"
include "simp1.mm"
include "s1cl.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "c1.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "elfzomin.mm"
include "syl.mm"
include "s1len.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "3adant2.mm"
include "ccatval2.mm"
include "syl3anc.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "nn0cnd.mm"
include "subidd.mm"
include "3ad2ant1.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "s1fv.mm"
include "3eqtrd.mm"

theorem ccats1val2
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ S e. V /\ I = ( # ` W ) ) -> ( ( W ++ <" S "> ) ` I ) = S )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cS
    cV
    wcel
    #
    cI
    cW
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    cI
    cW
    cS
    cs1
    #
    cconcat
    co
    cfv
    #
    cI
    @3
    cmin
    co
    #
    @6
    cfv
    #
    cc0
    @6
    cfv
    #
    cS
    @5
    @1
    @6
    @0
    wcel
    #
    cI
    @3
    @3
    @6
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @7
    @9
    wceq
    @1
    @2
    @4
    simp1
    @2
    @1
    @11
    @4
    cS
    cV
    s1cl
    3ad2ant2
    @1
    @4
    @15
    @2
    @1
    @4
    wa
    @15
    @3
    @14
    wcel
    #
    @1
    @16
    @4
    @1
    @3
    @3
    @3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @14
    @1
    @3
    cz
    wcel
    @3
    @18
    wcel
    @1
    @3
    cV
    cW
    lencl
    #
    nn0zd
    @3
    elfzomin
    syl
    @13
    @17
    @3
    cfzo
    @12
    c1
    @3
    caddc
    cS
    s1len
    oveq2i
    oveq2i
    syl6eleqr
    adantr
    @4
    @15
    @16
    wb
    @1
    cI
    @3
    @14
    eleq1
    adantl
    mpbird
    3adant2
    cV
    cW
    @6
    cI
    ccatval2
    syl3anc
    @5
    @8
    cc0
    @6
    @5
    @8
    @3
    @3
    cmin
    co
    #
    cc0
    @4
    @1
    @8
    @20
    wceq
    @2
    cI
    @3
    @3
    cmin
    oveq1
    3ad2ant3
    @1
    @2
    @20
    cc0
    wceq
    @4
    @1
    @3
    @1
    @3
    @19
    nn0cnd
    subidd
    3ad2ant1
    eqtrd
    fveq2d
    @2
    @1
    @10
    cS
    wceq
    @4
    cS
    cV
    s1fv
    3ad2ant2
    3eqtrd
end
