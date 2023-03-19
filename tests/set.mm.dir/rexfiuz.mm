include "cv.mm"
include "wral.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "wrex.mm"
include "wb.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "raleq.mm"
include "rexralbidv.mm"
include "bibi12d.mm"
include "weq.mm"
include "wne.mm"
include "cc0.mm"
include "0z.mm"
include "ne0ii.mm"
include "ral0.mm"
include "rgen2w.mm"
include "r19.2z.mm"
include "mp2an.mm"
include "2th.mm"
include "wi.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "anbi1.mm"
include "rexanuz.mm"
include "ralunb.mm"
include "ralbii.mm"
include "rexbii.mm"
include "cvv.mm"
include "vex.mm"
include "wsbc.mm"
include "ralsnsg.mm"
include "ralcom.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "sbcrex.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "ax-mp.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "3bitr4g.mm"
include "a1i.mm"
include "findcard2.mm"

theorem rexfiuz
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint j k
  disjoint j n
  disjoint A j
  disjoint k n
  disjoint A k
  disjoint A n
  disjoint j ph
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( A e. Fin -> ( E. j e. ZZ A. k e. ( ZZ>= ` j ) A. n e. A ph <-> A. n e. A E. j e. ZZ A. k e. ( ZZ>= ` j ) ph ) )

  proof
    wph
    vn
    vx
    cv
    #
    wral
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    vj
    cz
    wrex
    #
    wph
    vk
    @2
    wral
    #
    vj
    cz
    wrex
    #
    vn
    @0
    wral
    #
    wb
    wph
    vn
    c0
    wral
    #
    vk
    @2
    wral
    #
    vj
    cz
    wrex
    #
    @5
    vn
    c0
    wral
    #
    wb
    wph
    vn
    vy
    cv
    #
    wral
    #
    vk
    @2
    wral
    vj
    cz
    wrex
    #
    @5
    vn
    @11
    wral
    #
    wb
    #
    wph
    vn
    @11
    vz
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    vk
    @2
    wral
    #
    vj
    cz
    wrex
    #
    @5
    vn
    @18
    wral
    #
    wb
    #
    wph
    vn
    cA
    wral
    #
    vk
    @2
    wral
    vj
    cz
    wrex
    #
    @5
    vn
    cA
    wral
    #
    wb
    vx
    vy
    vz
    cA
    @0
    c0
    wceq
    #
    @3
    @9
    @6
    @10
    @27
    @1
    @7
    vj
    vk
    cz
    @2
    wph
    vn
    @0
    c0
    raleq
    rexralbidv
    @5
    vn
    @0
    c0
    raleq
    bibi12d
    vx
    vy
    weq
    #
    @3
    @13
    @6
    @14
    @28
    @1
    @12
    vj
    vk
    cz
    @2
    wph
    vn
    @0
    @11
    raleq
    rexralbidv
    @5
    vn
    @0
    @11
    raleq
    bibi12d
    @0
    @18
    wceq
    #
    @3
    @21
    @6
    @22
    @29
    @1
    @19
    vj
    vk
    cz
    @2
    wph
    vn
    @0
    @18
    raleq
    rexralbidv
    @5
    vn
    @0
    @18
    raleq
    bibi12d
    @0
    cA
    wceq
    #
    @3
    @25
    @6
    @26
    @30
    @1
    @24
    vj
    vk
    cz
    @2
    wph
    vn
    @0
    cA
    raleq
    rexralbidv
    @5
    vn
    @0
    cA
    raleq
    bibi12d
    @9
    @10
    cz
    c0
    wne
    @8
    vj
    cz
    wral
    @9
    cc0
    cz
    0z
    ne0ii
    @7
    vj
    vk
    cz
    @2
    wph
    vn
    ral0
    rgen2w
    @8
    vj
    cz
    r19.2z
    mp2an
    @5
    vn
    ral0
    2th
    @15
    @23
    wi
    @11
    cfn
    wcel
    @15
    @13
    @5
    vn
    @17
    wral
    #
    wa
    #
    @14
    @31
    wa
    @21
    @22
    @13
    @14
    @31
    anbi1
    @12
    wph
    vn
    @17
    wral
    #
    wa
    #
    vk
    @2
    wral
    #
    vj
    cz
    wrex
    @13
    @33
    vk
    @2
    wral
    #
    vj
    cz
    wrex
    #
    wa
    @21
    @32
    @12
    @33
    vj
    vk
    rexanuz
    @20
    @35
    vj
    cz
    @19
    @34
    vk
    @2
    wph
    vn
    @11
    @17
    ralunb
    ralbii
    rexbii
    @31
    @37
    @13
    @16
    cvv
    wcel
    #
    @31
    @37
    wb
    vz
    vex
    @38
    @31
    @5
    vn
    @16
    wsbc
    #
    @37
    @5
    vn
    @16
    cvv
    ralsnsg
    @38
    @37
    @4
    vn
    @16
    wsbc
    #
    vj
    cz
    wrex
    @39
    @38
    @36
    @40
    vj
    cz
    @36
    @4
    vn
    @17
    wral
    @38
    @40
    wph
    vk
    vn
    @2
    @17
    ralcom
    @4
    vn
    @16
    cvv
    ralsnsg
    syl5bb
    rexbidv
    @4
    vn
    vj
    @16
    cz
    sbcrex
    syl6rbbr
    bitrd
    ax-mp
    anbi2i
    3bitr4i
    @5
    vn
    @11
    @17
    ralunb
    3bitr4g
    a1i
    findcard2
end
