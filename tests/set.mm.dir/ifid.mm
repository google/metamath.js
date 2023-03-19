include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "iffalse.mm"
include "pm2.61i.mm"

theorem ifid
  let wph: wff ph
  let cA: class A


  assert |- if ( ph , A , A ) = A

  proof
    wph
    wph
    cA
    cA
    cif
    cA
    wceq
    wph
    cA
    cA
    iftrue
    wph
    cA
    cA
    iffalse
    pm2.61i
end
