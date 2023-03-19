include "cfv.mm"
include "cpws.mm"
include "co.mm"
include "cbs.mm"
include "ccrg.mm"
include "cvv.mm"
include "eqid.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crh.mm"
include "wf.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "pwselbas.mm"

theorem fveval1fvcl
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cU: class U
  let cM: class M
  let cO: class O
  let cY: class Y
  assume fveval1fvcl.q: |- O = ( eval1 ` R )
  assume fveval1fvcl.p: |- P = ( Poly1 ` R )
  assume fveval1fvcl.b: |- B = ( Base ` R )
  assume fveval1fvcl.u: |- U = ( Base ` P )
  assume fveval1fvcl.r: |- ( ph -> R e. CRing )
  assume fveval1fvcl.y: |- ( ph -> Y e. B )
  assume fveval1fvcl.m: |- ( ph -> M e. U )


  assert |- ( ph -> ( ( O ` M ) ` Y ) e. B )

  proof
    wph
    cB
    cB
    cY
    cM
    cO
    cfv
    #
    wph
    cB
    cR
    cB
    cR
    cB
    cpws
    co
    #
    cbs
    cfv
    #
    ccrg
    @0
    @1
    cvv
    @1
    eqid
    #
    fveval1fvcl.b
    @2
    eqid
    #
    fveval1fvcl.r
    cB
    cvv
    wcel
    wph
    cB
    cR
    cbs
    cfv
    cvv
    fveval1fvcl.b
    cR
    cbs
    fvex
    eqeltri
    a1i
    wph
    cU
    @2
    cM
    cO
    wph
    cR
    ccrg
    wcel
    cO
    cP
    @1
    crh
    co
    wcel
    cU
    @2
    cO
    wf
    fveval1fvcl.r
    cB
    cP
    cR
    @1
    cO
    fveval1fvcl.q
    fveval1fvcl.p
    @3
    fveval1fvcl.b
    evl1rhm
    cU
    @2
    cP
    @1
    cO
    fveval1fvcl.u
    @4
    rhmf
    3syl
    fveval1fvcl.m
    ffvelrnd
    pwselbas
    fveval1fvcl.y
    ffvelrnd
end
