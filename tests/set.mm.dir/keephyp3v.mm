include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "3bitrd.mm"
include "mpbii.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61i.mm"

theorem keephyp3v
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume keephyp3v.1: |- ( A = if ( ph , A , D ) -> ( rh <-> ch ) )
  assume keephyp3v.2: |- ( B = if ( ph , B , R ) -> ( ch <-> th ) )
  assume keephyp3v.3: |- ( C = if ( ph , C , S ) -> ( th <-> ta ) )
  assume keephyp3v.4: |- ( D = if ( ph , A , D ) -> ( et <-> ze ) )
  assume keephyp3v.5: |- ( R = if ( ph , B , R ) -> ( ze <-> si ) )
  assume keephyp3v.6: |- ( S = if ( ph , C , S ) -> ( si <-> ta ) )
  assume keephyp3v.7: |- rh
  assume keephyp3v.8: |- et


  assert |- ta

  proof
    wph
    wta
    wph
    wrh
    wta
    keephyp3v.7
    wph
    wrh
    wch
    wth
    wta
    wph
    cA
    wph
    cA
    cD
    cif
    #
    wceq
    wrh
    wch
    wb
    wph
    @0
    cA
    wph
    cA
    cD
    iftrue
    eqcomd
    keephyp3v.1
    syl
    wph
    cB
    wph
    cB
    cR
    cif
    #
    wceq
    wch
    wth
    wb
    wph
    @1
    cB
    wph
    cB
    cR
    iftrue
    eqcomd
    keephyp3v.2
    syl
    wph
    cC
    wph
    cC
    cS
    cif
    #
    wceq
    wth
    wta
    wb
    wph
    @2
    cC
    wph
    cC
    cS
    iftrue
    eqcomd
    keephyp3v.3
    syl
    3bitrd
    mpbii
    wph
    wn
    #
    wet
    wta
    keephyp3v.8
    @3
    wet
    wze
    wsi
    wta
    @3
    cD
    @0
    wceq
    wet
    wze
    wb
    @3
    @0
    cD
    wph
    cA
    cD
    iffalse
    eqcomd
    keephyp3v.4
    syl
    @3
    cR
    @1
    wceq
    wze
    wsi
    wb
    @3
    @1
    cR
    wph
    cB
    cR
    iffalse
    eqcomd
    keephyp3v.5
    syl
    @3
    cS
    @2
    wceq
    wsi
    wta
    wb
    @3
    @2
    cS
    wph
    cC
    cS
    iffalse
    eqcomd
    keephyp3v.6
    syl
    3bitrd
    mpbii
    pm2.61i
end
