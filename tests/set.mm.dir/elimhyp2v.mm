include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "bitrd.mm"
include "ibi.mm"
include "wn.mm"
include "iffalse.mm"
include "mpbii.mm"
include "pm2.61i.mm"

theorem elimhyp2v
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume elimhyp2v.1: |- ( A = if ( ph , A , C ) -> ( ph <-> ch ) )
  assume elimhyp2v.2: |- ( B = if ( ph , B , D ) -> ( ch <-> th ) )
  assume elimhyp2v.3: |- ( C = if ( ph , A , C ) -> ( ta <-> et ) )
  assume elimhyp2v.4: |- ( D = if ( ph , B , D ) -> ( et <-> th ) )
  assume elimhyp2v.5: |- ta


  assert |- th

  proof
    wph
    wth
    wph
    wth
    wph
    wph
    wch
    wth
    wph
    cA
    wph
    cA
    cC
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
    cC
    iftrue
    eqcomd
    elimhyp2v.1
    syl
    wph
    cB
    wph
    cB
    cD
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
    cD
    iftrue
    eqcomd
    elimhyp2v.2
    syl
    bitrd
    ibi
    wph
    wn
    #
    wta
    wth
    elimhyp2v.5
    @2
    wta
    wet
    wth
    @2
    cC
    @0
    wceq
    wta
    wet
    wb
    @2
    @0
    cC
    wph
    cA
    cC
    iffalse
    eqcomd
    elimhyp2v.3
    syl
    @2
    cD
    @1
    wceq
    wet
    wth
    wb
    @2
    @1
    cD
    wph
    cB
    cD
    iffalse
    eqcomd
    elimhyp2v.4
    syl
    bitrd
    mpbii
    pm2.61i
end
