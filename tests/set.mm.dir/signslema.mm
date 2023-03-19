include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wn.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "simpld.mm"
include "adantr.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "subeq0ad.mm"
include "biimpa.mm"
include "breq2d.mm"
include "wb.mm"
include "nn0red.mm"
include "posdifd.mm"
include "3bitr4rd.mm"
include "mpbid.mm"
include "0red.mm"
include "cr.mm"
include "wcel.mm"
include "resubcld.mm"
include "2pos.mm"
include "breq2.mm"
include "mpbiri.mm"
include "biimpar.mm"
include "sylan2.mm"
include "lttrd.mm"
include "mpbird.mm"
include "cpr.mm"
include "wo.mm"
include "sub4d.mm"
include "eqeltrrd.mm"
include "ovex.mm"
include "elpr.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "simprd.mm"
include "mtbird.mm"
include "caddc.mm"
include "cz.mm"
include "2z.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "dvdsaddr.mm"
include "sylancr.mm"
include "mtbid.mm"
include "2cnd.mm"
include "subaddd.mm"
include "jca.mm"

theorem signslema
  let wph: wff ph
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  assume signslema.1: |- ( ph -> E e. NN0 )
  assume signslema.2: |- ( ph -> F e. NN0 )
  assume signslema.3: |- ( ph -> G e. NN0 )
  assume signslema.4: |- ( ph -> H e. NN0 )
  assume signslema.5: |- ( ph -> ( E < G /\ -. 2 || ( G - E ) ) )
  assume signslema.6: |- ( ph -> ( ( H - G ) - ( F - E ) ) e. { 0 , 2 } )


  assert |- ( ph -> ( F < H /\ -. 2 || ( H - F ) ) )

  proof
    wph
    cF
    cH
    clt
    wbr
    #
    c2
    cH
    cF
    cmin
    co
    #
    cdvds
    wbr
    #
    wn
    #
    wph
    @1
    cG
    cE
    cmin
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    @0
    @5
    c2
    wceq
    #
    wph
    @6
    wa
    #
    cE
    cG
    clt
    wbr
    #
    @0
    wph
    @9
    @6
    wph
    @9
    c2
    @4
    cdvds
    wbr
    #
    wn
    #
    signslema.5
    simpld
    #
    adantr
    @8
    cc0
    @1
    clt
    wbr
    #
    cc0
    @4
    clt
    wbr
    #
    @0
    @9
    @8
    @1
    @4
    cc0
    clt
    wph
    @6
    @1
    @4
    wceq
    wph
    @1
    @4
    wph
    cH
    cF
    wph
    cH
    signslema.4
    nn0cnd
    #
    wph
    cF
    signslema.2
    nn0cnd
    #
    subcld
    #
    wph
    cG
    cE
    wph
    cG
    signslema.3
    nn0cnd
    #
    wph
    cE
    signslema.1
    nn0cnd
    #
    subcld
    #
    subeq0ad
    biimpa
    #
    breq2d
    wph
    @0
    @13
    wb
    #
    @6
    wph
    cF
    cH
    wph
    cF
    signslema.2
    nn0red
    #
    wph
    cH
    signslema.4
    nn0red
    #
    posdifd
    #
    adantr
    wph
    @9
    @14
    wb
    #
    @6
    wph
    cE
    cG
    wph
    cE
    signslema.1
    nn0red
    #
    wph
    cG
    signslema.3
    nn0red
    #
    posdifd
    #
    adantr
    3bitr4rd
    mpbid
    wph
    @7
    wa
    #
    @0
    @13
    @30
    cc0
    @4
    @1
    @30
    0red
    wph
    @4
    cr
    wcel
    @7
    wph
    cG
    cE
    @28
    @27
    resubcld
    #
    adantr
    wph
    @1
    cr
    wcel
    @7
    wph
    cH
    cF
    @24
    @23
    resubcld
    #
    adantr
    @30
    @9
    @14
    wph
    @9
    @7
    @12
    adantr
    wph
    @26
    @7
    @29
    adantr
    mpbid
    @7
    wph
    cc0
    @5
    clt
    wbr
    #
    @4
    @1
    clt
    wbr
    #
    @7
    @33
    cc0
    c2
    clt
    wbr
    2pos
    @5
    c2
    cc0
    clt
    breq2
    mpbiri
    wph
    @34
    @33
    wph
    @4
    @1
    @31
    @32
    posdifd
    biimpar
    sylan2
    lttrd
    wph
    @22
    @7
    @25
    adantr
    mpbird
    wph
    @5
    cc0
    c2
    cpr
    #
    wcel
    @6
    @7
    wo
    wph
    cH
    cG
    cmin
    co
    cF
    cE
    cmin
    co
    cmin
    co
    @5
    @35
    wph
    cH
    cG
    cF
    cE
    @15
    @18
    @16
    @19
    sub4d
    signslema.6
    eqeltrrd
    @5
    cc0
    c2
    @1
    @4
    cmin
    ovex
    elpr
    sylib
    #
    mpjaodan
    wph
    @6
    @3
    @7
    @8
    @2
    @10
    wph
    @11
    @6
    wph
    @9
    @11
    signslema.5
    simprd
    #
    adantr
    @8
    @1
    @4
    c2
    cdvds
    @21
    breq2d
    mtbird
    @30
    c2
    @4
    c2
    caddc
    co
    #
    cdvds
    wbr
    #
    @2
    wph
    @39
    wn
    @7
    wph
    @10
    @39
    @37
    wph
    c2
    cz
    wcel
    @4
    cz
    wcel
    @10
    @39
    wb
    2z
    wph
    cG
    cE
    wph
    cG
    signslema.3
    nn0zd
    wph
    cE
    signslema.1
    nn0zd
    zsubcld
    c2
    @4
    dvdsaddr
    sylancr
    mtbid
    adantr
    @30
    @38
    @1
    c2
    cdvds
    wph
    @7
    @38
    @1
    wceq
    wph
    @1
    @4
    c2
    @17
    @20
    wph
    2cnd
    subaddd
    biimpa
    breq2d
    mtbid
    @36
    mpjaodan
    jca
end
