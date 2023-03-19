include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "ccau.mm"
include "wral.mm"
include "isch2.mm"
include "wex.mm"
include "chil.mm"
include "ax-hcompl.mm"
include "rexex.mm"
include "syl.mm"
include "19.29.mm"
include "sylan2.mm"
include "id.mm"
include "imp.mm"
include "an12s.mm"
include "simprr.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "com12.mm"
include "df-rex.mm"
include "syl6ibr.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfim.mm"
include "bi2.04.mm"
include "hlimcaui.mm"
include "imim1i.mm"
include "weu.mm"
include "hlimeui.mm"
include "sylib.mm"
include "exancom.mm"
include "sylbb.mm"
include "eupick.mm"
include "syl2anc.mm"
include "syli.mm"
include "imim2i.mm"
include "sylbi.mm"
include "impd.mm"
include "alrimi.mm"
include "impbii.mm"
include "albii.mm"
include "df-ral.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem isch3
  let vx: setvar x
  let vf: setvar f
  let cH: class H

  disjoint f x
  disjoint H x
  disjoint H f
  assert |- ( H e. CH <-> ( H e. SH /\ A. f e. Cauchy ( f : NN --> H -> E. x e. H f ~~>v x ) ) )

  proof
    cH
    cch
    wcel
    cH
    csh
    wcel
    #
    cn
    cH
    vf
    cv
    #
    wf
    #
    @1
    vx
    cv
    #
    chli
    wbr
    #
    wa
    #
    @3
    cH
    wcel
    #
    wi
    #
    vx
    wal
    #
    vf
    wal
    #
    wa
    @0
    @2
    @4
    vx
    cH
    wrex
    #
    wi
    #
    vf
    ccau
    wral
    #
    wa
    vx
    vf
    cH
    isch2
    @9
    @12
    @0
    @9
    @1
    ccau
    wcel
    #
    @11
    wi
    #
    vf
    wal
    @12
    @8
    @14
    vf
    @8
    @14
    @8
    @13
    @11
    @8
    @13
    wa
    @7
    @4
    wa
    #
    vx
    wex
    #
    @11
    @13
    @8
    @4
    vx
    wex
    #
    @16
    @13
    @4
    vx
    chil
    wrex
    @17
    vx
    @1
    ax-hcompl
    @4
    vx
    chil
    rexex
    syl
    @7
    @4
    vx
    19.29
    sylan2
    @16
    @2
    @6
    @4
    wa
    #
    vx
    wex
    #
    @10
    @2
    @16
    @19
    @2
    @15
    @18
    vx
    @2
    @15
    @18
    @2
    @15
    wa
    @6
    @4
    @7
    @2
    @4
    @6
    @7
    @5
    @6
    @7
    id
    imp
    an12s
    @2
    @7
    @4
    simprr
    jca
    ex
    eximdv
    com12
    @4
    vx
    cH
    df-rex
    #
    syl6ibr
    syl
    ex
    @14
    @7
    vx
    @13
    @11
    vx
    @13
    vx
    nfv
    @2
    @10
    vx
    @2
    vx
    nfv
    @4
    vx
    cH
    nfre1
    nfim
    nfim
    @14
    @2
    @4
    @6
    @14
    @2
    @13
    @10
    wi
    #
    wi
    @2
    @4
    @6
    wi
    #
    wi
    @13
    @2
    @10
    bi2.04
    @21
    @22
    @2
    @4
    @21
    @10
    @6
    @4
    @13
    @10
    @3
    @1
    hlimcaui
    imim1i
    @10
    @4
    vx
    weu
    #
    @4
    @6
    wa
    vx
    wex
    #
    @22
    @10
    @17
    @23
    @4
    vx
    cH
    rexex
    vx
    @1
    hlimeui
    sylib
    @10
    @19
    @24
    @20
    @6
    @4
    vx
    exancom
    sylbb
    @4
    @6
    vx
    eupick
    syl2anc
    syli
    imim2i
    sylbi
    impd
    alrimi
    impbii
    albii
    @11
    vf
    ccau
    df-ral
    bitr4i
    anbi2i
    bitri
end
