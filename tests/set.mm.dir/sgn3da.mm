include "wi.mm"
include "cc0.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wtru.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "wb.mm"
include "csgn.mm"
include "cfv.mm"
include "cxr.mm"
include "wcel.mm"
include "sgnval.mm"
include "syl.mm"
include "eqeq2d.mm"
include "pm5.32i.mm"
include "eqcoms.mm"
include "bicomd.mm"
include "adantl.mm"
include "sylbir.mm"
include "expcom.mm"
include "pm5.74d.mm"
include "eqeq1.mm"
include "imbi1d.mm"
include "w3a.mm"
include "adantr.mm"
include "simp2.mm"
include "3expia.mm"
include "impbida.mm"
include "pm3.24.mm"
include "pm2.21i.mm"
include "expr.mm"
include "tbtru.mm"
include "sylib.mm"
include "anbi12d.mm"
include "ancom.mm"
include "truan.mm"
include "bitri.mm"
include "syl6bb.mm"
include "3adant3.mm"
include "3ad2ant3.mm"
include "bitr4d.mm"
include "3adant2.mm"
include "pm3.35.mm"
include "adantll.mm"
include "ifbothda.mm"
include "imp.mm"
include "ex.mm"
include "simp1.mm"
include "wo.mm"
include "wne.mm"
include "df-ne.mm"
include "0xr.mm"
include "xrlttri2.mm"
include "sylancl.mm"
include "syl5bbr.mm"
include "biimpa.mm"
include "ord.mm"
include "3impia.mm"
include "syl2anc.mm"
include "jca.mm"
include "trud.mm"

theorem sgn3da
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cA: class A
  assume sgn3da.0: |- ( ph -> A e. RR* )
  assume sgn3da.1: |- ( ( sgn ` A ) = 0 -> ( ps <-> ch ) )
  assume sgn3da.2: |- ( ( sgn ` A ) = 1 -> ( ps <-> th ) )
  assume sgn3da.3: |- ( ( sgn ` A ) = -u 1 -> ( ps <-> ta ) )
  assume sgn3da.4: |- ( ( ph /\ A = 0 ) -> ch )
  assume sgn3da.5: |- ( ( ph /\ 0 < A ) -> th )
  assume sgn3da.6: |- ( ( ph /\ A < 0 ) -> ta )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wi
    #
    cA
    cc0
    wceq
    #
    wph
    wch
    wi
    #
    wph
    cA
    cc0
    clt
    wbr
    #
    wta
    wi
    #
    @3
    wn
    #
    wth
    wi
    #
    wa
    #
    wi
    #
    @0
    wtru
    cc0
    @3
    c1
    cneg
    #
    c1
    cif
    #
    cc0
    @1
    cc0
    @10
    cif
    #
    wceq
    #
    wph
    wch
    wps
    wph
    @12
    wch
    wps
    wb
    #
    wph
    @12
    wa
    wph
    cc0
    cA
    csgn
    cfv
    #
    wceq
    #
    wa
    @13
    wph
    @15
    @12
    wph
    @14
    @11
    cc0
    wph
    cA
    cxr
    wcel
    #
    @14
    @11
    wceq
    sgn3da.0
    cA
    sgnval
    syl
    #
    eqeq2d
    pm5.32i
    @15
    @13
    wph
    @15
    wps
    wch
    wps
    wch
    wb
    @14
    cc0
    sgn3da.1
    eqcoms
    bicomd
    adantl
    sylbir
    expcom
    pm5.74d
    @10
    @11
    wceq
    #
    wph
    @7
    wps
    wph
    @18
    @7
    wps
    wb
    #
    wph
    @18
    wa
    wph
    @10
    @14
    wceq
    #
    wa
    @19
    wph
    @20
    @18
    wph
    @14
    @11
    @10
    @17
    eqeq2d
    pm5.32i
    wph
    @20
    @19
    @3
    @9
    @14
    wceq
    #
    @19
    wi
    c1
    @14
    wceq
    #
    @19
    wi
    @20
    @19
    wi
    wph
    @9
    c1
    @9
    @10
    wceq
    @21
    @20
    @19
    @9
    @10
    @14
    eqeq1
    imbi1d
    c1
    @10
    wceq
    @22
    @20
    @19
    c1
    @10
    @14
    eqeq1
    imbi1d
    wph
    @3
    @21
    @19
    wph
    @3
    @21
    w3a
    @7
    wta
    wps
    wph
    @3
    @7
    wta
    wb
    @21
    wph
    @3
    wa
    #
    @7
    wta
    wtru
    wa
    #
    wta
    @23
    @4
    wta
    @6
    wtru
    @23
    @4
    wta
    @23
    wta
    @4
    sgn3da.6
    adantr
    @23
    wta
    @3
    wta
    @23
    wta
    @3
    simp2
    3expia
    impbida
    @23
    @6
    @6
    wtru
    wb
    wph
    @3
    @5
    wth
    @3
    @5
    wa
    #
    wth
    wph
    @25
    wth
    @3
    pm3.24
    pm2.21i
    adantl
    expr
    @6
    tbtru
    sylib
    anbi12d
    @24
    wtru
    wta
    wa
    wta
    wta
    wtru
    ancom
    wta
    truan
    bitri
    syl6bb
    3adant3
    @21
    wph
    wps
    wta
    wb
    #
    @3
    @26
    @14
    @9
    sgn3da.3
    eqcoms
    3ad2ant3
    bitr4d
    3expia
    wph
    @5
    @22
    @19
    wph
    @5
    @22
    w3a
    @7
    wth
    wps
    wph
    @5
    @7
    wth
    wb
    @22
    wph
    @5
    wa
    #
    @7
    wtru
    wth
    wa
    wth
    @27
    @4
    wtru
    @6
    wth
    @27
    @4
    @4
    wtru
    wb
    wph
    @5
    @3
    wta
    wph
    @3
    wta
    @5
    sgn3da.6
    3adant2
    3expia
    @4
    tbtru
    sylib
    @27
    @6
    wth
    @5
    @6
    wth
    wph
    @5
    wth
    pm3.35
    adantll
    @27
    wth
    @5
    wth
    @27
    wth
    @5
    simp2
    3expia
    impbida
    anbi12d
    wth
    truan
    syl6bb
    3adant3
    @22
    wph
    wps
    wth
    wb
    #
    @5
    @28
    @14
    c1
    sgn3da.2
    eqcoms
    3ad2ant3
    bitr4d
    3expia
    ifbothda
    imp
    sylbir
    expcom
    pm5.74d
    @1
    @2
    wtru
    wph
    @1
    wch
    sgn3da.4
    expcom
    adantl
    @1
    wn
    #
    @8
    wtru
    wph
    @29
    @7
    wph
    @29
    wa
    #
    @4
    @6
    wph
    @4
    @29
    wph
    @3
    wta
    sgn3da.6
    ex
    adantr
    wph
    @29
    @5
    wth
    wph
    @29
    @5
    w3a
    wph
    cc0
    cA
    clt
    wbr
    #
    wth
    wph
    @29
    @5
    simp1
    wph
    @29
    @5
    @31
    @30
    @3
    @31
    wph
    @29
    @3
    @31
    wo
    #
    @29
    cA
    cc0
    wne
    #
    wph
    @32
    cA
    cc0
    df-ne
    wph
    @16
    cc0
    cxr
    wcel
    @33
    @32
    wb
    sgn3da.0
    0xr
    cA
    cc0
    xrlttri2
    sylancl
    syl5bbr
    biimpa
    ord
    3impia
    sgn3da.5
    syl2anc
    3expia
    jca
    expcom
    adantl
    ifbothda
    trud
end
