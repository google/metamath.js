include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "clsw.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "simpl.mm"
include "s1cl.mm"
include "adantl.mm"
include "s1nz.mm"
include "a1i.mm"
include "lswccatn0lsw.mm"
include "syl3anc.mm"
include "lsws1.mm"
include "eqtrd.mm"

theorem lswccats1
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ S e. V ) -> ( lastS ` ( W ++ <" S "> ) ) = S )

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
    wa
    #
    cW
    cS
    cs1
    #
    cconcat
    co
    clsw
    cfv
    #
    @4
    clsw
    cfv
    #
    cS
    @3
    @1
    @4
    @0
    wcel
    #
    @4
    c0
    wne
    #
    @5
    @6
    wceq
    @1
    @2
    simpl
    @2
    @7
    @1
    cS
    cV
    s1cl
    adantl
    @8
    @3
    cS
    s1nz
    a1i
    cW
    @4
    cV
    lswccatn0lsw
    syl3anc
    @2
    @6
    cS
    wceq
    @1
    cS
    cV
    lsws1
    adantl
    eqtrd
end
