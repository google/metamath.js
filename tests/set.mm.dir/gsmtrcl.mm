include "cgsu.mm"
include "co.mm"
include "cpsgn.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cfn.mm"
include "cword.mm"
include "wa.mm"
include "eqid.mm"
include "psgneldm2i.mm"
include "cid.mm"
include "cdif.mm"
include "wi.mm"
include "psgneldm.mm"
include "ax-1.mm"
include "adantr.mm"
include "sylbi.mm"
include "mpcom.mm"

theorem gsmtrcl
  let cB: class B
  let cS: class S
  let cT: class T
  let cN: class N
  let cW: class W
  assume gsmtrcl.s: |- S = ( SymGrp ` N )
  assume gsmtrcl.b: |- B = ( Base ` S )
  assume gsmtrcl.t: |- T = ran ( pmTrsp ` N )


  assert |- ( ( N e. Fin /\ W e. Word T ) -> ( S gsum W ) e. B )

  proof
    cS
    cW
    cgsu
    co
    #
    cN
    cpsgn
    cfv
    #
    cdm
    wcel
    #
    cN
    cfn
    wcel
    cW
    cT
    cword
    wcel
    wa
    #
    @0
    cB
    wcel
    #
    cN
    cT
    cS
    @1
    cfn
    cW
    gsmtrcl.s
    gsmtrcl.t
    @1
    eqid
    #
    psgneldm2i
    @2
    @4
    @0
    cid
    cdif
    cdm
    cfn
    wcel
    #
    wa
    @3
    @4
    wi
    #
    cB
    cN
    @0
    cS
    @1
    gsmtrcl.s
    @5
    gsmtrcl.b
    psgneldm
    @4
    @7
    @6
    @4
    @3
    ax-1
    adantr
    sylbi
    mpcom
end
