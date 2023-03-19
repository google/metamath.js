include "clnr.mm"
include "wcel.mm"
include "crg.mm"
include "crglmod.mm"
include "cfv.mm"
include "clnm.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "islnr.mm"
include "clmod.mm"
include "wb.mm"
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
include "islnm2.mm"
include "baib.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem islnr2
  let cB: class B
  let cR: class R
  let cU: class U
  let vg: setvar g
  let vi: setvar i
  let cN: class N
  assume islnr2.b: |- B = ( Base ` R )
  assume islnr2.u: |- U = ( LIdeal ` R )
  assume islnr2.n: |- N = ( RSpan ` R )

  disjoint g i
  disjoint R i
  disjoint R g
  disjoint N i
  disjoint N g
  disjoint U i
  disjoint U g
  disjoint B i
  disjoint B g
  assert |- ( R e. LNoeR <-> ( R e. Ring /\ A. i e. U E. g e. ( ~P B i^i Fin ) i = ( N ` g ) ) )

  proof
    cR
    clnr
    wcel
    cR
    crg
    wcel
    #
    cR
    crglmod
    cfv
    #
    clnm
    wcel
    #
    wa
    @0
    vi
    cv
    vg
    cv
    cN
    cfv
    wceq
    vg
    cB
    cpw
    cfn
    cin
    wrex
    vi
    cU
    wral
    #
    wa
    cR
    islnr
    @0
    @2
    @3
    @0
    @1
    clmod
    wcel
    #
    @2
    @3
    wb
    cR
    rlmlmod
    @2
    @4
    @3
    cB
    cU
    vg
    vi
    @1
    cN
    cB
    cR
    cbs
    cfv
    @1
    cbs
    cfv
    islnr2.b
    cR
    rlmbas
    eqtri
    cU
    cR
    clidl
    cfv
    @1
    clss
    cfv
    islnr2.u
    cR
    lidlval
    eqtri
    cN
    cR
    crsp
    cfv
    @1
    clspn
    cfv
    islnr2.n
    cR
    rspval
    eqtri
    islnm2
    baib
    syl
    pm5.32i
    bitri
end
