include "c0.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "eqid.mm"
include "rint0.mm"
include "ax-mp.mm"
include "wss.mm"
include "wcel.mm"
include "0ss.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "0ex.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "inteq.mm"
include "ineq2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "mpan2.mm"
include "syl5eqelr.mm"
include "wne.mm"
include "w3a.mm"
include "cpw.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "sstrd.mm"
include "simp3.mm"
include "rintn0.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "eqeltrrd.mm"
include "ismred.mm"

theorem ismred2
  let wph: wff ph
  let cC: class C
  let cX: class X
  let vs: setvar s
  assume ismred2.ss: |- ( ph -> C C_ ~P X )
  assume ismred2.in: |- ( ( ph /\ s C_ C ) -> ( X i^i |^| s ) e. C )

  disjoint ph s
  disjoint C s
  disjoint X s
  assert |- ( ph -> C e. ( Moore ` X ) )

  proof
    wph
    cC
    cX
    vs
    ismred2.ss
    wph
    cX
    cX
    c0
    cint
    #
    cin
    #
    cC
    c0
    c0
    wceq
    @1
    cX
    wceq
    c0
    eqid
    cX
    c0
    rint0
    ax-mp
    wph
    c0
    cC
    wss
    #
    @1
    cC
    wcel
    #
    cC
    0ss
    wph
    vs
    cv
    #
    cC
    wss
    #
    wa
    #
    cX
    @4
    cint
    #
    cin
    #
    cC
    wcel
    #
    wi
    wph
    @2
    wa
    #
    @3
    wi
    vs
    c0
    0ex
    @4
    c0
    wceq
    #
    @6
    @10
    @9
    @3
    @11
    @5
    @2
    wph
    @4
    c0
    cC
    sseq1
    anbi2d
    @11
    @8
    @1
    cC
    @11
    @7
    @0
    cX
    @4
    c0
    inteq
    ineq2d
    eleq1d
    imbi12d
    ismred2.in
    vtocl
    mpan2
    syl5eqelr
    wph
    @5
    @4
    c0
    wne
    #
    w3a
    #
    @8
    @7
    cC
    @13
    @4
    cX
    cpw
    #
    wss
    @12
    @8
    @7
    wceq
    @13
    @4
    cC
    @14
    wph
    @5
    @12
    simp2
    wph
    @5
    cC
    @14
    wss
    @12
    ismred2.ss
    3ad2ant1
    sstrd
    wph
    @5
    @12
    simp3
    cX
    @4
    rintn0
    syl2anc
    wph
    @5
    @9
    @12
    ismred2.in
    3adant3
    eqeltrrd
    ismred
end
