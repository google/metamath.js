include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "bitrd.mm"
include "mpbii.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61i.mm"

theorem keephyp2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume keephyp2v.1: |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) )
  assume keephyp2v.2: |- ( B = if ( ph , B , D ) -> ( ch <-> th ) )
  assume keephyp2v.3: |- ( C = if ( ph , A , C ) -> ( ta <-> et ) )
  assume keephyp2v.4: |- ( D = if ( ph , B , D ) -> ( et <-> th ) )
  assume keephyp2v.5: |- ps
  assume keephyp2v.6: |- ta


  assert |- th

  proof
    wph
    wth
    wph
    wps
    wth
    keephyp2v.5
    wph
    wps
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
    wps
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
    keephyp2v.1
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
    keephyp2v.2
    syl
    bitrd
    mpbii
    wph
    wn
    #
    wta
    wth
    keephyp2v.6
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
    keephyp2v.3
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
    keephyp2v.4
    syl
    bitrd
    mpbii
    pm2.61i
end
