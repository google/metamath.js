include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cc.mm"
include "wss.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprr.mm"
include "readdcld.mm"
include "rexrd.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elico1.mm"
include "mp2an.mm"
include "simp2bi.mm"
include "syl.mm"
include "addge0d.mm"
include "ltpnf.mm"
include "syl3anbrc.mm"
include "0e0icopnf.mm"
include "fsumcllem.mm"

theorem fsumrp0cl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fsumrp0cl.1: |- ( ph -> A e. Fin )
  assume fsumrp0cl.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> sum_ k e. A B e. ( 0 [,) +oo ) )

  proof
    wph
    vx
    vy
    cA
    cB
    cc0
    cpnf
    cico
    co
    #
    vk
    @0
    cc
    wss
    wph
    @0
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    a1i
    wph
    vx
    cv
    #
    @0
    wcel
    #
    vy
    cv
    #
    @0
    wcel
    #
    wa
    wa
    #
    @1
    @3
    caddc
    co
    #
    cxr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    cpnf
    clt
    wbr
    #
    @6
    @0
    wcel
    #
    @5
    @6
    @5
    @1
    @3
    @5
    @0
    cr
    @1
    rge0ssre
    wph
    @2
    @4
    simprl
    #
    sseldi
    #
    @5
    @0
    cr
    @3
    rge0ssre
    wph
    @2
    @4
    simprr
    #
    sseldi
    #
    readdcld
    #
    rexrd
    @5
    @1
    @3
    @12
    @14
    @5
    @2
    cc0
    @1
    cle
    wbr
    #
    @11
    @2
    @1
    cxr
    wcel
    #
    @16
    @1
    cpnf
    clt
    wbr
    #
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @2
    @17
    @16
    @18
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @1
    elico1
    mp2an
    simp2bi
    syl
    @5
    @4
    cc0
    @3
    cle
    wbr
    #
    @13
    @4
    @3
    cxr
    wcel
    #
    @21
    @3
    cpnf
    clt
    wbr
    #
    @19
    @20
    @4
    @22
    @21
    @23
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @3
    elico1
    mp2an
    simp2bi
    syl
    addge0d
    @5
    @6
    cr
    wcel
    @9
    @15
    @6
    ltpnf
    syl
    @19
    @20
    @10
    @7
    @8
    @9
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @6
    elico1
    mp2an
    syl3anbrc
    fsumrp0cl.1
    fsumrp0cl.2
    cc0
    @0
    wcel
    wph
    0e0icopnf
    a1i
    fsumcllem
end
