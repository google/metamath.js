include "csle.mm"
include "wbr.mm"
include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cslt.mm"
include "ccnv.mm"
include "wn.mm"
include "cxp.mm"
include "cdif.mm"
include "df-sle.mm"
include "breqi.mm"
include "brdif.mm"
include "brxp.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "ibar.mm"
include "brcnvg.mm"
include "notbid.mm"
include "bitr3d.mm"
include "syl5bb.mm"

theorem slenlt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A <_s B <-> -. B <s A ) )

  proof
    cA
    cB
    csle
    wbr
    #
    cA
    csur
    wcel
    cB
    csur
    wcel
    wa
    #
    cA
    cB
    cslt
    ccnv
    #
    wbr
    #
    wn
    #
    wa
    #
    @1
    cB
    cA
    cslt
    wbr
    #
    wn
    #
    @0
    cA
    cB
    csur
    csur
    cxp
    #
    @2
    cdif
    #
    wbr
    cA
    cB
    @8
    wbr
    #
    @4
    wa
    @5
    cA
    cB
    csle
    @9
    df-sle
    breqi
    cA
    cB
    @8
    @2
    brdif
    @10
    @1
    @4
    cA
    cB
    csur
    csur
    brxp
    anbi1i
    3bitri
    @1
    @4
    @5
    @7
    @1
    @4
    ibar
    @1
    @3
    @6
    cA
    cB
    csur
    csur
    cslt
    brcnvg
    notbid
    bitr3d
    syl5bb
end
