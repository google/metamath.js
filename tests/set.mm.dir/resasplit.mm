include "wfn.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cdif.mm"
include "fnresdm.mm"
include "uneq12.mm"
include "syl2an.mm"
include "3adant3.mm"
include "simp3.mm"
include "uneq1d.mm"
include "uneq2d.mm"
include "inundif.mm"
include "reseq2i.mm"
include "resundi.mm"
include "eqtr3i.mm"
include "incom.mm"
include "uneq1i.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "syl6reqr.mm"
include "un4.mm"
include "syl6eq.mm"
include "unidm.mm"
include "eqtr3d.mm"

theorem resasplit
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F Fn A /\ G Fn B /\ ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( F u. G ) = ( ( F |` ( A i^i B ) ) u. ( ( F |` ( A \ B ) ) u. ( G |` ( B \ A ) ) ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    cF
    cA
    cB
    cin
    #
    cres
    #
    cG
    @2
    cres
    #
    wceq
    #
    w3a
    #
    cF
    cA
    cres
    #
    cG
    cB
    cres
    #
    cun
    #
    cF
    cG
    cun
    #
    @3
    cF
    cA
    cB
    cdif
    #
    cres
    #
    cG
    cB
    cA
    cdif
    #
    cres
    #
    cun
    #
    cun
    #
    @0
    @1
    @9
    @10
    wceq
    #
    @5
    @0
    @7
    cF
    wceq
    @8
    cG
    wceq
    @17
    @1
    cA
    cF
    fnresdm
    cB
    cG
    fnresdm
    @7
    cF
    @8
    cG
    uneq12
    syl2an
    3adant3
    @6
    @9
    @3
    @3
    cun
    #
    @15
    cun
    #
    @16
    @6
    @9
    @3
    @12
    cun
    #
    @3
    @14
    cun
    #
    cun
    #
    @19
    @6
    @22
    @20
    @4
    @14
    cun
    #
    cun
    @9
    @6
    @21
    @23
    @20
    @6
    @3
    @4
    @14
    @0
    @1
    @5
    simp3
    uneq1d
    uneq2d
    @7
    @20
    @8
    @23
    cF
    @2
    @11
    cun
    #
    cres
    @7
    @20
    @24
    cA
    cF
    cA
    cB
    inundif
    reseq2i
    cF
    @2
    @11
    resundi
    eqtr3i
    cG
    @2
    @13
    cun
    #
    cres
    @8
    @23
    @25
    cB
    cG
    @25
    cB
    cA
    cin
    #
    @13
    cun
    cB
    @2
    @26
    @13
    cA
    cB
    incom
    uneq1i
    cB
    cA
    inundif
    eqtri
    reseq2i
    cG
    @2
    @13
    resundi
    eqtr3i
    uneq12i
    syl6reqr
    @3
    @12
    @3
    @14
    un4
    syl6eq
    @18
    @3
    @15
    @3
    unidm
    uneq1i
    syl6eq
    eqtr3d
end
