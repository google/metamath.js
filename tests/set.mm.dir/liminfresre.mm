include "cr.mm"
include "cres.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "clsi.mm"
include "cfv.mm"
include "wceq.mm"
include "rge0ssre.mm"
include "resabs1i.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cvv.mm"
include "0red.mm"
include "eqid.mm"
include "resexd.mm"
include "liminfresico.mm"
include "3eqtr3d.mm"

theorem liminfresre
  let wph: wff ph
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume liminfresre.1: |- ( ph -> F e. V )


  assert |- ( ph -> ( liminf ` ( F |` RR ) ) = ( liminf ` F ) )

  proof
    wph
    cF
    cr
    cres
    #
    cc0
    cpnf
    cico
    co
    #
    cres
    #
    clsi
    cfv
    #
    cF
    @1
    cres
    #
    clsi
    cfv
    #
    @0
    clsi
    cfv
    cF
    clsi
    cfv
    @3
    @5
    wceq
    wph
    @2
    @4
    clsi
    cF
    @1
    cr
    rge0ssre
    resabs1i
    fveq2i
    a1i
    wph
    @0
    cc0
    cvv
    @1
    wph
    0red
    #
    @1
    eqid
    #
    wph
    cF
    cr
    cV
    liminfresre.1
    resexd
    liminfresico
    wph
    cF
    cc0
    cV
    @1
    @6
    @7
    liminfresre.1
    liminfresico
    3eqtr3d
end
