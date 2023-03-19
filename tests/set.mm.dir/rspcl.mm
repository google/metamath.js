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
include "clidl.mm"
include "clss.mm"
include "lidlval.mm"
include "crsp.mm"
include "clspn.mm"
include "rspval.mm"
include "lspcl.mm"
include "sylan.mm"

theorem rspcl
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cK: class K
  assume rspcl.k: |- K = ( RSpan ` R )
  assume rspcl.b: |- B = ( Base ` R )
  assume rspcl.u: |- U = ( LIdeal ` R )


  assert |- ( ( R e. Ring /\ G C_ B ) -> ( K ` G ) e. U )

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
    cK
    cfv
    cU
    wcel
    cR
    rlmlmod
    cU
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
    cU
    cR
    clidl
    cfv
    @0
    clss
    cfv
    rspcl.u
    cR
    lidlval
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
    lspcl
    sylan
end
