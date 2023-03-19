include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cres.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0lefi.mm"
include "wb.mm"
include "wcel.mm"
include "elpwinss.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbiia.mm"
include "a1i.mm"
include "bitrd.mm"

theorem sge0lefimpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume sge0lefimpt.xph: |- F/ x ph
  assume sge0lefimpt.a: |- ( ph -> A e. V )
  assume sge0lefimpt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0lefimpt.c: |- ( ph -> C e. RR* )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( ( sum^ ` ( x e. A |-> B ) ) <_ C <-> A. y e. ( ~P A i^i Fin ) ( sum^ ` ( x e. y |-> B ) ) <_ C ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    cC
    cle
    wbr
    @0
    vy
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    cC
    cle
    wbr
    #
    vy
    cA
    cpw
    cfn
    cin
    #
    wral
    #
    vx
    @1
    cB
    cmpt
    #
    csumge0
    cfv
    #
    cC
    cle
    wbr
    #
    vy
    @5
    wral
    #
    wph
    vy
    cC
    @0
    cV
    cA
    sge0lefimpt.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0lefimpt.xph
    sge0lefimpt.b
    @0
    eqid
    fmptdf
    sge0lefimpt.c
    sge0lefi
    @6
    @10
    wb
    wph
    @4
    @9
    vy
    @5
    @1
    @5
    wcel
    #
    @3
    @8
    cC
    cle
    @11
    @2
    @7
    csumge0
    @11
    vx
    cA
    @1
    cB
    @1
    cA
    cfn
    elpwinss
    resmptd
    fveq2d
    breq1d
    ralbiia
    a1i
    bitrd
end
