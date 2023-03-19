include "crg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmod.mm"
include "wss.mm"
include "rlmlmod.mm"
include "cbs.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "crsp.mm"
include "clspn.mm"
include "rspval.mm"
include "lspssid.mm"
include "sylan.mm"

theorem rspssid
  let cB: class B
  let cR: class R
  let cG: class G
  let cK: class K
  assume rspcl.k: |- K = ( RSpan ` R )
  assume rspcl.b: |- B = ( Base ` R )


  assert |- ( ( R e. Ring /\ G C_ B ) -> G C_ ( K ` G ) )

  proof
    cR
    crg
    wcel
    cR
    crglmod
    cfv
    #
    clmod
    wcel
    cG
    cB
    wss
    cG
    cG
    cK
    cfv
    wss
    cR
    rlmlmod
    cG
    cK
    cB
    @0
    cB
    cR
    cbs
    cfv
    @0
    cbs
    cfv
    rspcl.b
    cR
    rlmbas
    eqtri
    cK
    cR
    crsp
    cfv
    @0
    clspn
    cfv
    rspcl.k
    cR
    rspval
    eqtri
    lspssid
    sylan
end
