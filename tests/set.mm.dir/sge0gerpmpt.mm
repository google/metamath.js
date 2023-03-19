include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "cv.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "csumge0.mm"
include "cfv.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cres.mm"
include "wi.mm"
include "elpwinss.mm"
include "resmptd.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "biimpd.mm"
include "adantl.mm"
include "reximdva.mm"
include "mpd.mm"
include "sge0gerp.mm"

theorem sge0gerpmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume sge0gerpmpt.xph: |- F/ x ph
  assume sge0gerpmpt.a: |- ( ph -> A e. V )
  assume sge0gerpmpt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0gerpmpt.c: |- ( ph -> C e. RR* )
  assume sge0gerpmpt.rp: |- ( ( ph /\ y e. RR+ ) -> E. z e. ( ~P A i^i Fin ) C <_ ( ( sum^ ` ( x e. z |-> B ) ) +e y ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> C <_ ( sum^ ` ( x e. A |-> B ) ) )

  proof
    wph
    vy
    vz
    cC
    vx
    cA
    cB
    cmpt
    #
    cV
    cA
    sge0gerpmpt.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0gerpmpt.xph
    sge0gerpmpt.b
    @0
    eqid
    fmptdf
    sge0gerpmpt.c
    wph
    vy
    cv
    #
    crp
    wcel
    wa
    #
    cC
    vx
    vz
    cv
    #
    cB
    cmpt
    #
    csumge0
    cfv
    #
    @1
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cA
    cpw
    cfn
    cin
    #
    wrex
    cC
    @0
    @3
    cres
    #
    csumge0
    cfv
    #
    @1
    cxad
    co
    #
    cle
    wbr
    #
    vz
    @8
    wrex
    sge0gerpmpt.rp
    @2
    @7
    @12
    vz
    @8
    @3
    @8
    wcel
    #
    @7
    @12
    wi
    @2
    @13
    @7
    @12
    @13
    @6
    @11
    cC
    cle
    @13
    @5
    @10
    @1
    cxad
    @13
    @4
    @9
    csumge0
    @13
    @9
    @4
    @13
    vx
    cA
    @3
    cB
    @3
    cA
    cfn
    elpwinss
    resmptd
    eqcomd
    fveq2d
    oveq1d
    breq2d
    biimpd
    adantl
    reximdva
    mpd
    sge0gerp
end
