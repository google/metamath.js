include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "bitrd.mm"
include "3bitrd.mm"
include "ibi.mm"
include "wn.mm"
include "iffalse.mm"
include "mpbii.mm"
include "pm2.61i.mm"

theorem elimhyp4v
  let wph: wff ph
  let wps: wff ps
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
  let cF: class F
  let cG: class G
  assume elimhyp4v.1: |- ( A = if ( ph , A , D ) -> ( ph <-> ch ) )
  assume elimhyp4v.2: |- ( B = if ( ph , B , R ) -> ( ch <-> th ) )
  assume elimhyp4v.3: |- ( C = if ( ph , C , S ) -> ( th <-> ta ) )
  assume elimhyp4v.4: |- ( F = if ( ph , F , G ) -> ( ta <-> ps ) )
  assume elimhyp4v.5: |- ( D = if ( ph , A , D ) -> ( et <-> ze ) )
  assume elimhyp4v.6: |- ( R = if ( ph , B , R ) -> ( ze <-> si ) )
  assume elimhyp4v.7: |- ( S = if ( ph , C , S ) -> ( si <-> rh ) )
  assume elimhyp4v.8: |- ( G = if ( ph , F , G ) -> ( rh <-> ps ) )
  assume elimhyp4v.9: |- et


  assert |- ps

  proof
    wph
    wps
    wph
    wps
    wph
    wph
    wth
    wta
    wps
    wph
    wph
    wch
    wth
    wph
    cA
    wph
    cA
    cD
    cif
    #
    wceq
    wph
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
    elimhyp4v.1
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
    elimhyp4v.2
    syl
    bitrd
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
    elimhyp4v.3
    syl
    wph
    cF
    wph
    cF
    cG
    cif
    #
    wceq
    wta
    wps
    wb
    wph
    @3
    cF
    wph
    cF
    cG
    iftrue
    eqcomd
    elimhyp4v.4
    syl
    3bitrd
    ibi
    wph
    wn
    #
    wet
    wps
    elimhyp4v.9
    @4
    wet
    wsi
    wrh
    wps
    @4
    wet
    wze
    wsi
    @4
    cD
    @0
    wceq
    wet
    wze
    wb
    @4
    @0
    cD
    wph
    cA
    cD
    iffalse
    eqcomd
    elimhyp4v.5
    syl
    @4
    cR
    @1
    wceq
    wze
    wsi
    wb
    @4
    @1
    cR
    wph
    cB
    cR
    iffalse
    eqcomd
    elimhyp4v.6
    syl
    bitrd
    @4
    cS
    @2
    wceq
    wsi
    wrh
    wb
    @4
    @2
    cS
    wph
    cC
    cS
    iffalse
    eqcomd
    elimhyp4v.7
    syl
    @4
    cG
    @3
    wceq
    wrh
    wps
    wb
    @4
    @3
    cG
    wph
    cF
    cG
    iffalse
    eqcomd
    elimhyp4v.8
    syl
    3bitrd
    mpbii
    pm2.61i
end
