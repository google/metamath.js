include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "reflcl.mm"
include "adantl.mm"
include "simpr.mm"
include "simpl.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "flle.mm"
include "lemul2ad.mm"
include "cz.mm"
include "wb.mm"
include "remulcld.mm"
include "nn0z.mm"
include "flcl.mm"
include "zmulcl.mm"
include "syl2an.mm"
include "flge.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem flmulnn0
  let cA: class A
  let cN: class N


  assert |- ( ( N e. NN0 /\ A e. RR ) -> ( N x. ( |_ ` A ) ) <_ ( |_ ` ( N x. A ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cr
    wcel
    #
    wa
    #
    cN
    cA
    cfl
    cfv
    #
    cmul
    co
    #
    cN
    cA
    cmul
    co
    #
    cle
    wbr
    #
    @4
    @5
    cfl
    cfv
    cle
    wbr
    #
    @2
    @3
    cA
    cN
    @1
    @3
    cr
    wcel
    @0
    cA
    reflcl
    adantl
    @0
    @1
    simpr
    #
    @2
    cN
    @0
    @1
    simpl
    #
    nn0red
    #
    @2
    cN
    @9
    nn0ge0d
    @1
    @3
    cA
    cle
    wbr
    @0
    cA
    flle
    adantl
    lemul2ad
    @2
    @5
    cr
    wcel
    @4
    cz
    wcel
    #
    @6
    @7
    wb
    @2
    cN
    cA
    @10
    @8
    remulcld
    @0
    cN
    cz
    wcel
    @3
    cz
    wcel
    @11
    @1
    cN
    nn0z
    cA
    flcl
    cN
    @3
    zmulcl
    syl2an
    @5
    @4
    flge
    syl2anc
    mpbid
end
