include "c0.mm"
include "cdm.mm"
include "cuni.mm"
include "eqid.mm"
include "cpw.mm"
include "wcel.mm"
include "0elpw.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "in0.mm"
include "fveq2i.mm"
include "dif0.mm"
include "oveq12i.mm"
include "ome0.mm"
include "adantr.mm"
include "oveq1d.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "iccssxr.mm"
include "come.mm"
include "wss.mm"
include "elpwi.mm"
include "adantl.mm"
include "omecl.mm"
include "sseldi.mm"
include "xaddid2d.mm"
include "3eqtrd.mm"
include "carageneld.mm"

theorem caragen0
  let wph: wff ph
  let cS: class S
  let cO: class O
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume caragen0.o: |- ( ph -> O e. OutMeas )
  assume caragen0.s: |- S = ( CaraGen ` O )


  assert |- ( ph -> (/) e. S )

  proof
    wph
    cS
    c0
    cO
    cO
    cdm
    cuni
    #
    va
    caragen0.o
    @0
    eqid
    #
    caragen0.s
    c0
    @0
    cpw
    #
    wcel
    wph
    @0
    0elpw
    a1i
    wph
    va
    cv
    #
    @2
    wcel
    #
    wa
    #
    @3
    c0
    cin
    #
    cO
    cfv
    #
    @3
    c0
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    c0
    cO
    cfv
    #
    @3
    cO
    cfv
    #
    cxad
    co
    #
    cc0
    @12
    cxad
    co
    @12
    @10
    @13
    wceq
    @5
    @7
    @11
    @9
    @12
    cxad
    @6
    c0
    cO
    @3
    in0
    fveq2i
    @8
    @3
    cO
    @3
    dif0
    fveq2i
    oveq12i
    a1i
    @5
    @11
    cc0
    @12
    cxad
    wph
    @11
    cc0
    wceq
    @4
    wph
    cO
    caragen0.o
    ome0
    adantr
    oveq1d
    @5
    @12
    @5
    cc0
    cpnf
    cicc
    co
    cxr
    @12
    cc0
    cpnf
    iccssxr
    @5
    @3
    cO
    @0
    wph
    cO
    come
    wcel
    @4
    caragen0.o
    adantr
    @1
    @4
    @3
    @0
    wss
    wph
    @3
    @0
    elpwi
    adantl
    omecl
    sseldi
    xaddid2d
    3eqtrd
    carageneld
end
