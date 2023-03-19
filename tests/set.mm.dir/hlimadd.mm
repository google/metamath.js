include "cva.mm"
include "co.mm"
include "cno.mm"
include "cmv.mm"
include "ccom.mm"
include "cmopn.mm"
include "cfv.mm"
include "clm.mm"
include "wbr.mm"
include "chil.mm"
include "cn.mm"
include "cmap.mm"
include "wcel.mm"
include "chli.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cxmt.mm"
include "ctopon.mm"
include "csm.mm"
include "cop.mm"
include "eqid.mm"
include "hhims.mm"
include "hhxmet.mm"
include "mopntopon.mm"
include "mp1i.mm"
include "cres.mm"
include "hhnv.mm"
include "df-hba.mm"
include "h2hlm.mm"
include "resss.mm"
include "eqsstri.mm"
include "ssbri.mm"
include "syl.mm"
include "cnv.mm"
include "ctx.mm"
include "ccn.mm"
include "hhva.mm"
include "vacn.mm"
include "lmcn2.mm"
include "wf.mm"
include "cv.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "hvaddcl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "ax-hilex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "breqi.mm"
include "ovex.mm"
include "brres.mm"
include "bitri.mm"
include "sylanbrc.mm"

theorem hlimadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  assume hlimadd.3: |- ( ph -> F : NN --> ~H )
  assume hlimadd.4: |- ( ph -> G : NN --> ~H )
  assume hlimadd.5: |- ( ph -> F ~~>v A )
  assume hlimadd.6: |- ( ph -> G ~~>v B )
  assume hlimadd.7: |- H = ( n e. NN |-> ( ( F ` n ) +h ( G ` n ) ) )

  disjoint F n
  disjoint G n
  disjoint n ph
  assert |- ( ph -> H ~~>v ( A +h B ) )

  proof
    wph
    cH
    cA
    cB
    cva
    co
    #
    cno
    cmv
    ccom
    #
    cmopn
    cfv
    #
    clm
    cfv
    #
    wbr
    #
    cH
    chil
    cn
    cmap
    co
    #
    wcel
    #
    cH
    @0
    chli
    wbr
    #
    wph
    cA
    cB
    vn
    cF
    cG
    cH
    @2
    @2
    c1
    @2
    cva
    chil
    chil
    cn
    nnuz
    wph
    1zzd
    @1
    chil
    cxmt
    cfv
    wcel
    @2
    chil
    ctopon
    cfv
    wcel
    wph
    @1
    cva
    csm
    cop
    cno
    cop
    #
    @8
    eqid
    #
    @1
    @8
    @9
    @1
    eqid
    hhims
    #
    hhxmet
    @1
    @2
    chil
    @2
    eqid
    #
    mopntopon
    mp1i
    #
    @12
    hlimadd.3
    hlimadd.4
    wph
    cF
    cA
    chli
    wbr
    cF
    cA
    @3
    wbr
    hlimadd.5
    chli
    @3
    cF
    cA
    chli
    @3
    @5
    cres
    #
    @3
    @1
    @8
    @2
    @9
    @8
    @9
    hhnv
    #
    df-hba
    @10
    @11
    h2hlm
    #
    @3
    @5
    resss
    eqsstri
    #
    ssbri
    syl
    wph
    cG
    cB
    chli
    wbr
    cG
    cB
    @3
    wbr
    hlimadd.6
    chli
    @3
    cG
    cB
    @16
    ssbri
    syl
    @8
    cnv
    wcel
    cva
    @2
    @2
    ctx
    co
    @2
    ccn
    co
    wcel
    wph
    @14
    @1
    @8
    cva
    @2
    @10
    @11
    @8
    @9
    hhva
    vacn
    mp1i
    hlimadd.7
    lmcn2
    wph
    cn
    chil
    cH
    wf
    @6
    wph
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    @17
    cG
    cfv
    #
    cva
    co
    #
    chil
    cH
    wph
    @17
    cn
    wcel
    wa
    @18
    chil
    wcel
    @19
    chil
    wcel
    @20
    chil
    wcel
    wph
    cn
    chil
    @17
    cF
    hlimadd.3
    ffvelrnda
    wph
    cn
    chil
    @17
    cG
    hlimadd.4
    ffvelrnda
    @18
    @19
    hvaddcl
    syl2anc
    hlimadd.7
    fmptd
    chil
    cn
    cH
    ax-hilex
    nnex
    elmap
    sylibr
    @7
    cH
    @0
    @13
    wbr
    @4
    @6
    wa
    cH
    @0
    chli
    @13
    @15
    breqi
    cH
    @0
    @3
    @5
    cA
    cB
    cva
    ovex
    brres
    bitri
    sylanbrc
end
