include "csn.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "cdif.mm"
include "cun.mm"
include "reseq1i.mm"
include "resundir.mm"
include "c0.mm"
include "cin.mm"
include "wceq.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "resdisj.mm"
include "ax-mp.mm"
include "uneq2i.mm"
include "un0.mm"
include "fveq1i.mm"
include "wcel.mm"
include "snid.mm"
include "fvres.mm"
include "fvsn.mm"
include "3eqtr3i.mm"

theorem fvsnun1
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  assume fvsnun.1: |- A e. _V
  assume fvsnun.2: |- B e. _V
  assume fvsnun.3: |- G = ( { <. A , B >. } u. ( F |` ( C \ { A } ) ) )


  assert |- ( G ` A ) = B

  proof
    cA
    cG
    cA
    csn
    #
    cres
    #
    cfv
    #
    cA
    cA
    cB
    cop
    csn
    #
    @0
    cres
    #
    cfv
    #
    cA
    cG
    cfv
    #
    cB
    cA
    @1
    @4
    @1
    @3
    cF
    cC
    @0
    cdif
    #
    cres
    #
    cun
    #
    @0
    cres
    #
    @4
    cG
    @9
    @0
    fvsnun.3
    reseq1i
    @10
    @4
    @8
    @0
    cres
    #
    cun
    #
    @4
    @3
    @8
    @0
    resundir
    @12
    @4
    c0
    cun
    @4
    @11
    c0
    @4
    @7
    @0
    cin
    #
    c0
    wceq
    @11
    c0
    wceq
    @13
    @0
    @7
    cin
    c0
    @7
    @0
    incom
    @0
    cC
    disjdif
    eqtri
    @7
    @0
    cF
    resdisj
    ax-mp
    uneq2i
    @4
    un0
    eqtri
    eqtri
    eqtri
    fveq1i
    cA
    @0
    wcel
    #
    @2
    @6
    wceq
    cA
    fvsnun.1
    snid
    #
    cA
    @0
    cG
    fvres
    ax-mp
    @5
    cA
    @3
    cfv
    #
    cB
    @14
    @5
    @16
    wceq
    @15
    cA
    @0
    @3
    fvres
    ax-mp
    cA
    cB
    fvsnun.1
    fvsnun.2
    fvsn
    eqtri
    3eqtr3i
end
