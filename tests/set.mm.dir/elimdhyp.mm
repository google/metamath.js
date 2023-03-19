include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "mpbid.mm"
include "wn.mm"
include "iffalse.mm"
include "mpbii.mm"
include "pm2.61i.mm"

theorem elimdhyp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let cA: class A
  let cB: class B
  assume elimdhyp.1: |- ( ph -> ps )
  assume elimdhyp.2: |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) )
  assume elimdhyp.3: |- ( B = if ( ph , A , B ) -> ( th <-> ch ) )
  assume elimdhyp.4: |- th


  assert |- ch

  proof
    wph
    wch
    wph
    wps
    wch
    elimdhyp.1
    wph
    cA
    wph
    cA
    cB
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
    cB
    iftrue
    eqcomd
    elimdhyp.2
    syl
    mpbid
    wph
    wn
    #
    wth
    wch
    elimdhyp.4
    @1
    cB
    @0
    wceq
    wth
    wch
    wb
    @1
    @0
    cB
    wph
    cA
    cB
    iffalse
    eqcomd
    elimdhyp.3
    syl
    mpbii
    pm2.61i
end
