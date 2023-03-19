include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "fzosplitsn.mm"
include "difeq1d.mm"
include "difun2.mm"
include "syl6eq.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "fzonel.mm"
include "disjsn.mm"
include "mpbir.mm"
include "disjdif2.mm"
include "mp1i.mm"
include "eqtrd.mm"

theorem fzodif2
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( ( M ..^ ( N + 1 ) ) \ { N } ) = ( M ..^ N ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cN
    c1
    caddc
    co
    cfzo
    co
    #
    cN
    csn
    #
    cdif
    #
    cM
    cN
    cfzo
    co
    #
    @2
    cdif
    #
    @4
    @0
    @3
    @4
    @2
    cun
    #
    @2
    cdif
    @5
    @0
    @1
    @6
    @2
    cM
    cN
    fzosplitsn
    difeq1d
    @4
    @2
    difun2
    syl6eq
    @4
    @2
    cin
    c0
    wceq
    #
    @5
    @4
    wceq
    @0
    @7
    cN
    @4
    wcel
    wn
    cM
    cN
    fzonel
    @4
    cN
    disjsn
    mpbir
    @4
    @2
    disjdif2
    mp1i
    eqtrd
end
