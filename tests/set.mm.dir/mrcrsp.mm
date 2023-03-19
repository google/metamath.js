include "crg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmod.mm"
include "wceq.mm"
include "rlmlmod.mm"
include "clidl.mm"
include "clss.mm"
include "lidlval.mm"
include "eqtri.mm"
include "crsp.mm"
include "clspn.mm"
include "rspval.mm"
include "mrclsp.mm"
include "syl.mm"

theorem mrcrsp
  let cR: class R
  let cU: class U
  let cF: class F
  let cK: class K
  assume mrcrsp.u: |- U = ( LIdeal ` R )
  assume mrcrsp.k: |- K = ( RSpan ` R )
  assume mrcrsp.f: |- F = ( mrCls ` U )


  assert |- ( R e. Ring -> K = F )

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
    cK
    cF
    wceq
    cR
    rlmlmod
    cU
    cF
    cK
    @0
    cU
    cR
    clidl
    cfv
    @0
    clss
    cfv
    mrcrsp.u
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
    mrcrsp.k
    cR
    rspval
    eqtri
    mrcrsp.f
    mrclsp
    syl
end
