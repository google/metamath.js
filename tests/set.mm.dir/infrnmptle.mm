include "cmpt.mm"
include "crn.mm"
include "nfv.mm"
include "cxr.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfrex.mm"
include "w3a.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "id.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "breqtrd.mm"
include "breq1.mm"
include "rspcev.mm"
include "3exp.mm"
include "rexlimd.mm"
include "adantr.mm"
include "mpd.mm"
include "infleinf2.mm"

theorem infrnmptle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  assume infrnmptle.x: |- F/ x ph
  assume infrnmptle.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume infrnmptle.c: |- ( ( ph /\ x e. A ) -> C e. RR* )
  assume infrnmptle.l: |- ( ( ph /\ x e. A ) -> B <_ C )

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
  assert |- ( ph -> inf ( ran ( x e. A |-> B ) , RR* , < ) <_ inf ( ran ( x e. A |-> C ) , RR* , < ) )

  proof
    wph
    vy
    vz
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    vx
    cA
    cC
    cmpt
    #
    crn
    #
    wph
    vy
    nfv
    wph
    vz
    nfv
    wph
    vx
    cA
    cB
    cxr
    @0
    infrnmptle.x
    @0
    eqid
    #
    infrnmptle.b
    rnmptssd
    wph
    vx
    cA
    cC
    cxr
    @2
    infrnmptle.x
    @2
    eqid
    #
    infrnmptle.c
    rnmptssd
    wph
    vy
    cv
    #
    @3
    wcel
    #
    wa
    @6
    cC
    wceq
    #
    vx
    cA
    wrex
    #
    vz
    cv
    #
    @6
    cle
    wbr
    #
    vz
    @1
    wrex
    #
    @7
    @9
    wph
    @7
    @9
    @6
    cvv
    wcel
    @7
    @9
    wb
    vy
    vex
    vx
    cA
    cC
    @6
    @2
    cvv
    @5
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @9
    @12
    wi
    @7
    wph
    @8
    @12
    vx
    cA
    infrnmptle.x
    @11
    vx
    vz
    @1
    vx
    @0
    vx
    cA
    cB
    nfmpt1
    nfrn
    @11
    vx
    nfv
    nfrex
    wph
    vx
    cv
    cA
    wcel
    #
    @8
    @12
    wph
    @13
    @8
    w3a
    #
    cB
    @1
    wcel
    #
    cB
    @6
    cle
    wbr
    #
    @12
    wph
    @13
    @15
    @8
    wph
    @13
    wa
    @13
    cB
    cxr
    wcel
    @15
    wph
    @13
    simpr
    infrnmptle.b
    vx
    cA
    cB
    @0
    cxr
    @4
    elrnmpt1
    syl2anc
    3adant3
    @14
    cB
    cC
    @6
    cle
    wph
    @13
    cB
    cC
    cle
    wbr
    @8
    infrnmptle.l
    3adant3
    @8
    wph
    cC
    @6
    wceq
    @13
    @8
    @6
    cC
    @8
    id
    eqcomd
    3ad2ant3
    breqtrd
    @11
    @16
    vz
    cB
    @1
    @10
    cB
    @6
    cle
    breq1
    rspcev
    syl2anc
    3exp
    rexlimd
    adantr
    mpd
    infleinf2
end
