include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "eleq2.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "wo.mm"
include "wa.mm"
include "id.mm"
include "orim12d.mm"
include "wb.mm"
include "elsuc2g.mm"
include "bicomd.mm"
include "adantl.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "om2uzsuci.mm"
include "cuz.mm"
include "om2uzuzi.mm"
include "cz.mm"
include "eluzelz.mm"
include "zleltp1.mm"
include "syl2an.mm"
include "cr.mm"
include "syl.mm"
include "zred.mm"
include "leloe.mm"
include "3bitr2rd.mm"
include "syl5ib.mm"
include "expcom.mm"
include "a2d.mm"
include "finds.mm"
include "impcom.mm"

theorem om2uzlti
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  assert |- ( ( A e. _om /\ B e. _om ) -> ( A e. B -> ( G ` A ) < ( G ` B ) ) )

  proof
    cB
    com
    wcel
    cA
    com
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cG
    cfv
    #
    cB
    cG
    cfv
    #
    clt
    wbr
    #
    wi
    #
    @0
    cA
    vz
    cv
    #
    wcel
    #
    @2
    @6
    cG
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    @0
    cA
    c0
    wcel
    #
    @2
    c0
    cG
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    @0
    cA
    vy
    cv
    #
    wcel
    #
    @2
    @15
    cG
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    @0
    cA
    @15
    csuc
    #
    wcel
    #
    @2
    @20
    cG
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    @0
    @5
    wi
    vz
    vy
    cB
    @6
    c0
    wceq
    #
    @10
    @14
    @0
    @25
    @7
    @11
    @9
    @13
    @6
    c0
    cA
    eleq2
    @25
    @8
    @12
    @2
    clt
    @6
    c0
    cG
    fveq2
    breq2d
    imbi12d
    imbi2d
    @6
    @15
    wceq
    #
    @10
    @19
    @0
    @26
    @7
    @16
    @9
    @18
    @6
    @15
    cA
    eleq2
    @26
    @8
    @17
    @2
    clt
    @6
    @15
    cG
    fveq2
    breq2d
    imbi12d
    imbi2d
    @6
    @20
    wceq
    #
    @10
    @24
    @0
    @27
    @7
    @21
    @9
    @23
    @6
    @20
    cA
    eleq2
    @27
    @8
    @22
    @2
    clt
    @6
    @20
    cG
    fveq2
    breq2d
    imbi12d
    imbi2d
    @6
    cB
    wceq
    #
    @10
    @5
    @0
    @28
    @7
    @1
    @9
    @4
    @6
    cB
    cA
    eleq2
    @28
    @8
    @3
    @2
    clt
    @6
    cB
    cG
    fveq2
    breq2d
    imbi12d
    imbi2d
    @14
    @0
    @11
    @13
    cA
    noel
    pm2.21i
    a1i
    @15
    com
    wcel
    #
    @0
    @19
    @24
    @0
    @29
    @19
    @24
    wi
    @19
    @16
    cA
    @15
    wceq
    #
    wo
    #
    @18
    @2
    @17
    wceq
    #
    wo
    #
    wi
    @0
    @29
    wa
    #
    @24
    @19
    @16
    @18
    @30
    @32
    @19
    id
    @30
    @32
    wi
    @19
    cA
    @15
    cG
    fveq2
    a1i
    orim12d
    @34
    @31
    @21
    @33
    @23
    @29
    @31
    @21
    wb
    @0
    @29
    @21
    @31
    cA
    @15
    com
    elsuc2g
    bicomd
    adantl
    @34
    @23
    @2
    @17
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @2
    @17
    cle
    wbr
    #
    @33
    @29
    @23
    @36
    wb
    @0
    @29
    @22
    @35
    @2
    clt
    vx
    @15
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzsuci
    breq2d
    adantl
    @0
    @2
    cC
    cuz
    cfv
    #
    wcel
    #
    @17
    @38
    wcel
    #
    @37
    @36
    wb
    #
    @29
    vx
    cA
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    #
    vx
    @15
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    #
    @39
    @2
    cz
    wcel
    #
    @17
    cz
    wcel
    #
    @41
    @40
    cC
    @2
    eluzelz
    #
    cC
    @17
    eluzelz
    #
    @2
    @17
    zleltp1
    syl2an
    syl2an
    @0
    @2
    cr
    wcel
    @17
    cr
    wcel
    @37
    @33
    wb
    @29
    @0
    @2
    @0
    @39
    @44
    @42
    @46
    syl
    zred
    @29
    @17
    @29
    @40
    @45
    @43
    @47
    syl
    zred
    @2
    @17
    leloe
    syl2an
    3bitr2rd
    imbi12d
    syl5ib
    expcom
    a2d
    finds
    impcom
end
