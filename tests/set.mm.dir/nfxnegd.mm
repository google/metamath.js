include "cxne.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "cneg.mm"
include "cif.mm"
include "df-xneg.mm"
include "nfcvd.mm"
include "nfeqd.mm"
include "nfnegd.mm"
include "nfifd.mm"
include "nfcxfrd.mm"

theorem nfxnegd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume nfxnegd.1: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x -e A )

  proof
    wph
    vx
    cA
    cxne
    cA
    cpnf
    wceq
    #
    cmnf
    cA
    cmnf
    wceq
    #
    cpnf
    cA
    cneg
    #
    cif
    #
    cif
    cA
    df-xneg
    wph
    @0
    vx
    cmnf
    @3
    wph
    vx
    cA
    cpnf
    nfxnegd.1
    wph
    vx
    cpnf
    nfcvd
    #
    nfeqd
    wph
    vx
    cmnf
    nfcvd
    #
    wph
    @1
    vx
    cpnf
    @2
    wph
    vx
    cA
    cmnf
    nfxnegd.1
    @5
    nfeqd
    @4
    wph
    vx
    cA
    nfxnegd.1
    nfnegd
    nfifd
    nfifd
    nfcxfrd
end
