include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "cun.mm"
include "reseq1i.mm"
include "resundir.mm"
include "c0.mm"
include "cin.mm"
include "wceq.mm"
include "disjdif.mm"
include "wfn.mm"
include "wb.mm"
include "fnsn.mm"
include "fnresdisj.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "residm.mm"
include "uneq12i.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtri.mm"
include "fveq1i.mm"
include "fvres.mm"
include "3eqtr3a.mm"

theorem fvsnun2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume fvsnun.1: |- A e. _V
  assume fvsnun.2: |- B e. _V
  assume fvsnun.3: |- G = ( { <. A , B >. } u. ( F |` ( C \ { A } ) ) )


  assert |- ( D e. ( C \ { A } ) -> ( G ` D ) = ( F ` D ) )

  proof
    cD
    cC
    cA
    csn
    #
    cdif
    #
    wcel
    cD
    cG
    @1
    cres
    #
    cfv
    cD
    cF
    @1
    cres
    #
    cfv
    cD
    cG
    cfv
    cD
    cF
    cfv
    cD
    @2
    @3
    @2
    cA
    cB
    cop
    csn
    #
    @3
    cun
    #
    @1
    cres
    @4
    @1
    cres
    #
    @3
    @1
    cres
    #
    cun
    #
    @3
    cG
    @5
    @1
    fvsnun.3
    reseq1i
    @4
    @3
    @1
    resundir
    @8
    c0
    @3
    cun
    @3
    c0
    cun
    @3
    @6
    c0
    @7
    @3
    @0
    @1
    cin
    c0
    wceq
    #
    @6
    c0
    wceq
    #
    @0
    cC
    disjdif
    @4
    @0
    wfn
    @9
    @10
    wb
    cA
    cB
    fvsnun.1
    fvsnun.2
    fnsn
    @0
    @1
    @4
    fnresdisj
    ax-mp
    mpbi
    cF
    @1
    residm
    uneq12i
    c0
    @3
    uncom
    @3
    un0
    3eqtri
    3eqtri
    fveq1i
    cD
    @1
    cG
    fvres
    cD
    @1
    cF
    fvres
    3eqtr3a
end
