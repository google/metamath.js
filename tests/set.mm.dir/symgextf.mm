include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "simplll.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "simpllr.mm"
include "wne.mm"
include "simpr.mm"
include "df-ne.mm"
include "biimpri.mm"
include "anim12i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "csymg.mm"
include "eqid.mm"
include "symgfv.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "ifclda.mm"
include "fmptd.mm"

theorem symgextf
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cZ: class Z
  assume symgext.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgext.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint K x
  disjoint N x
  disjoint S x
  disjoint Z x
  assert |- ( ( K e. N /\ Z e. S ) -> E : N --> N )

  proof
    cK
    cN
    wcel
    #
    cZ
    cS
    wcel
    #
    wa
    #
    vx
    cN
    vx
    cv
    #
    cK
    wceq
    #
    cK
    @3
    cZ
    cfv
    #
    cif
    cN
    cE
    @2
    @3
    cN
    wcel
    #
    wa
    #
    @4
    cK
    @5
    cN
    @0
    @1
    @6
    @4
    simplll
    @7
    @4
    wn
    #
    wa
    #
    @5
    cN
    cK
    csn
    #
    @9
    @1
    @3
    cN
    @10
    cdif
    #
    wcel
    #
    @5
    @11
    wcel
    @0
    @1
    @6
    @8
    simpllr
    @9
    @6
    @3
    cK
    wne
    #
    wa
    @12
    @7
    @6
    @8
    @13
    @2
    @6
    simpr
    @13
    @8
    @3
    cK
    df-ne
    biimpri
    anim12i
    @3
    cN
    cK
    eldifsn
    sylibr
    @11
    cS
    cZ
    @11
    csymg
    cfv
    #
    @3
    @14
    eqid
    symgext.s
    symgfv
    syl2anc
    eldifad
    ifclda
    symgext.e
    fmptd
end
