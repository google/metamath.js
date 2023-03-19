include "crg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmod.mm"
include "wss.mm"
include "rlmlmod.mm"
include "clidl.mm"
include "clss.mm"
include "lidlval.mm"
include "eqtri.mm"
include "crsp.mm"
include "clspn.mm"
include "rspval.mm"
include "lspssp.mm"
include "syl3an1.mm"

theorem rspssp
  let cR: class R
  let cU: class U
  let cG: class G
  let cI: class I
  let cK: class K
  assume rspcl.k: |- K = ( RSpan ` R )
  assume rspssp.u: |- U = ( LIdeal ` R )


  assert |- ( ( R e. Ring /\ I e. U /\ G C_ I ) -> ( K ` G ) C_ I )

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
    cI
    cU
    wcel
    cG
    cI
    wss
    cG
    cK
    cfv
    cI
    wss
    cR
    rlmlmod
    cU
    cG
    cI
    cK
    @0
    cU
    cR
    clidl
    cfv
    @0
    clss
    cfv
    rspssp.u
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
    lspssp
    syl3an1
end
