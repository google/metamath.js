include "cmnd.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "wa.mm"
include "wfo.mm"
include "cplusf.mm"
include "cfv.mm"
include "eqid.mm"
include "mndpfo.mm"
include "adantr.mm"
include "wceq.mm"
include "wb.mm"
include "plusfeq.mm"
include "eqcomd.mm"
include "adantl.mm"
include "foeq1.mm"
include "syl.mm"
include "mpbird.mm"

theorem mndfo
  let cB: class B
  let c.pl: class .+
  let cG: class G
  assume mndfo.b: |- B = ( Base ` G )
  assume mndfo.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ .+ Fn ( B X. B ) ) -> .+ : ( B X. B ) -onto-> B )

  proof
    cG
    cmnd
    wcel
    #
    c.pl
    cB
    cB
    cxp
    #
    wfn
    #
    wa
    #
    @1
    cB
    c.pl
    wfo
    #
    @1
    cB
    cG
    cplusf
    cfv
    #
    wfo
    #
    @0
    @6
    @2
    cB
    @5
    cG
    mndfo.b
    @5
    eqid
    #
    mndpfo
    adantr
    @3
    c.pl
    @5
    wceq
    #
    @4
    @6
    wb
    @2
    @8
    @0
    @2
    @5
    c.pl
    cB
    c.pl
    @5
    cG
    mndfo.b
    mndfo.p
    @7
    plusfeq
    eqcomd
    adantl
    @1
    cB
    c.pl
    @5
    foeq1
    syl
    mpbird
end
