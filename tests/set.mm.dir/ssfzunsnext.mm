include "cfz.mm"
include "co.mm"
include "wss.mm"
include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "csn.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "simpl.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "simp3.mm"
include "simp1.mm"
include "ifcld.mm"
include "adantr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "cr.mm"
include "zred.mm"
include "zre.mm"
include "3ad2ant1.mm"
include "anim12i.mm"
include "ancomd.mm"
include "3adant2.mm"
include "min2.mm"
include "syl.mm"
include "elfzle1.mm"
include "letrd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "simp2.mm"
include "3ad2ant2.mm"
include "elfzle2.mm"
include "3adant1.mm"
include "max2.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"
include "sstrd.mm"
include "3jca.mm"
include "min1.mm"
include "max1.mm"
include "jca.mm"
include "elfz2.mm"
include "snssd.mm"
include "unssd.mm"

theorem ssfzunsnext
  let cS: class S
  let cI: class I
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( ( S C_ ( M ... N ) /\ ( M e. ZZ /\ N e. ZZ /\ I e. ZZ ) ) -> ( S u. { I } ) C_ ( if ( I <_ M , I , M ) ... if ( I <_ N , N , I ) ) )

  proof
    cS
    cM
    cN
    cfz
    co
    #
    wss
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cI
    cz
    wcel
    #
    w3a
    #
    wa
    #
    cS
    cI
    csn
    cI
    cM
    cle
    wbr
    #
    cI
    cM
    cif
    #
    cI
    cN
    cle
    wbr
    #
    cN
    cI
    cif
    #
    cfz
    co
    #
    @6
    cS
    @0
    @11
    @1
    @5
    simpl
    @5
    @0
    @11
    wss
    @1
    @5
    vk
    @0
    @11
    @5
    vk
    cv
    #
    @0
    wcel
    #
    @12
    @11
    wcel
    #
    @5
    @13
    wa
    #
    @12
    @8
    cuz
    cfv
    wcel
    #
    @10
    @12
    cuz
    cfv
    wcel
    #
    @14
    @15
    @8
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @8
    @12
    cle
    wbr
    @16
    @5
    @18
    @13
    @5
    @7
    cI
    cM
    cz
    @2
    @3
    @4
    simp3
    #
    @2
    @3
    @4
    simp1
    ifcld
    #
    adantr
    @13
    @19
    @5
    @12
    cM
    cN
    elfzelz
    #
    adantl
    #
    @15
    @8
    cM
    @12
    @5
    @8
    cr
    wcel
    @13
    @5
    @8
    @21
    zred
    adantr
    @5
    cM
    cr
    wcel
    #
    @13
    @2
    @3
    @24
    @4
    cM
    zre
    #
    3ad2ant1
    adantr
    @13
    @12
    cr
    wcel
    @5
    @13
    @12
    @22
    zred
    adantl
    #
    @15
    cI
    cr
    wcel
    #
    @24
    wa
    #
    @8
    cM
    cle
    wbr
    @5
    @28
    @13
    @2
    @4
    @28
    @3
    @2
    @4
    wa
    @24
    @27
    @2
    @24
    @4
    @27
    @25
    cI
    zre
    #
    anim12i
    #
    ancomd
    3adant2
    adantr
    cI
    cM
    min2
    syl
    @13
    cM
    @12
    cle
    wbr
    @5
    @12
    cM
    cN
    elfzle1
    adantl
    letrd
    @8
    @12
    eluz2
    syl3anbrc
    @15
    @19
    @10
    cz
    wcel
    #
    @12
    @10
    cle
    wbr
    @17
    @23
    @5
    @31
    @13
    @5
    @9
    cN
    cI
    cz
    @2
    @3
    @4
    simp2
    @20
    ifcld
    #
    adantr
    @15
    @12
    cN
    @10
    @26
    @5
    cN
    cr
    wcel
    #
    @13
    @3
    @2
    @33
    @4
    cN
    zre
    #
    3ad2ant2
    adantr
    @5
    @10
    cr
    wcel
    @13
    @5
    @10
    @32
    zred
    adantr
    @13
    @12
    cN
    cle
    wbr
    @5
    @12
    cM
    cN
    elfzle2
    adantl
    @5
    cN
    @10
    cle
    wbr
    #
    @13
    @5
    @27
    @33
    wa
    #
    @35
    @5
    @33
    @27
    @3
    @4
    @33
    @27
    wa
    #
    @2
    @3
    @33
    @4
    @27
    @34
    @29
    anim12i
    3adant1
    #
    ancomd
    cI
    cN
    max2
    syl
    adantr
    letrd
    @12
    @10
    eluz2
    syl3anbrc
    @12
    @8
    @10
    elfzuzb
    sylanbrc
    ex
    ssrdv
    adantl
    sstrd
    @6
    cI
    @11
    @6
    @18
    @31
    @4
    w3a
    @8
    cI
    cle
    wbr
    #
    cI
    @10
    cle
    wbr
    #
    wa
    cI
    @11
    wcel
    @6
    @18
    @31
    @4
    @5
    @18
    @1
    @21
    adantl
    @5
    @31
    @1
    @32
    adantl
    @5
    @4
    @1
    @20
    adantl
    3jca
    @6
    @39
    @40
    @6
    @28
    @39
    @6
    @24
    @27
    @5
    @24
    @27
    wa
    #
    @1
    @2
    @4
    @41
    @3
    @30
    3adant2
    adantl
    ancomd
    cI
    cM
    min1
    syl
    @6
    @36
    @40
    @6
    @33
    @27
    @5
    @37
    @1
    @38
    adantl
    ancomd
    cI
    cN
    max1
    syl
    jca
    cI
    @8
    @10
    elfz2
    sylanbrc
    snssd
    unssd
end
