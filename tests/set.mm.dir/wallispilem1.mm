include "cc0.mm"
include "cpi.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cexp.mm"
include "citg.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cmpt.mm"
include "cibl.mm"
include "0re.mm"
include "a1i.mm"
include "pire.mm"
include "peano2nn0.mm"
include "syl.mm"
include "iblioosinexp.mm"
include "syl3anc.mm"
include "wa.mm"
include "elioore.mm"
include "resincld.mm"
include "adantl.mm"
include "adantr.mm"
include "reexpcld.mm"
include "cuz.mm"
include "cz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "peano2uz.mm"
include "wbr.mm"
include "clt.mm"
include "jctil.mm"
include "sinq12gt0.mm"
include "ltle.mm"
include "sylc.mm"
include "cneg.mm"
include "sinbnd.mm"
include "simprd.mm"
include "leexp2rd.mm"
include "itgle.mm"
include "wceq.mm"
include "oveq2.mm"
include "itgeq2dv.mm"
include "itgex.mm"
include "fvmpt.mm"
include "3brtr4d.mm"

theorem wallispilem1
  let wph: wff ph
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cN: class N
  let vk: setvar k
  assume wallispilem1.1: |- I = ( n e. NN0 |-> S. ( 0 (,) _pi ) ( ( sin ` x ) ^ n ) _d x )
  assume wallispilem1.2: |- ( ph -> N e. NN0 )

  disjoint n x
  disjoint N n
  disjoint N x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( I ` ( N + 1 ) ) <_ ( I ` N ) )

  proof
    wph
    vx
    cc0
    cpi
    cioo
    co
    #
    vx
    cv
    #
    csin
    cfv
    #
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    citg
    #
    vx
    @0
    @2
    cN
    cexp
    co
    #
    citg
    #
    @3
    cI
    cfv
    #
    cN
    cI
    cfv
    #
    cle
    wph
    vx
    @0
    @4
    @6
    wph
    cc0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @3
    cn0
    wcel
    #
    vx
    @0
    @4
    cmpt
    cibl
    wcel
    @10
    wph
    0re
    a1i
    #
    @11
    wph
    pire
    a1i
    #
    wph
    cN
    cn0
    wcel
    #
    @12
    wallispilem1.2
    cN
    peano2nn0
    syl
    #
    vx
    cc0
    cpi
    @3
    iblioosinexp
    syl3anc
    wph
    @10
    @11
    @15
    vx
    @0
    @6
    cmpt
    cibl
    wcel
    @13
    @14
    wallispilem1.2
    vx
    cc0
    cpi
    cN
    iblioosinexp
    syl3anc
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    @3
    @17
    @2
    cr
    wcel
    #
    wph
    @17
    @1
    @1
    cc0
    cpi
    elioore
    #
    resincld
    #
    adantl
    #
    wph
    @12
    @17
    @16
    adantr
    reexpcld
    @18
    @2
    cN
    @22
    wph
    @15
    @17
    wallispilem1.2
    adantr
    #
    reexpcld
    @18
    @2
    cN
    @3
    @22
    @23
    wph
    @3
    cN
    cuz
    cfv
    #
    wcel
    #
    @17
    wph
    cN
    @24
    wcel
    #
    @25
    wph
    cN
    cz
    wcel
    @26
    wph
    cN
    wallispilem1.2
    nn0zd
    cN
    uzid
    syl
    cN
    cN
    peano2uz
    syl
    adantr
    @17
    cc0
    @2
    cle
    wbr
    #
    wph
    @17
    @10
    @19
    wa
    cc0
    @2
    clt
    wbr
    @27
    @17
    @19
    @10
    @21
    0re
    jctil
    @1
    sinq12gt0
    cc0
    @2
    ltle
    sylc
    adantl
    @17
    @2
    c1
    cle
    wbr
    #
    wph
    @17
    c1
    cneg
    @2
    cle
    wbr
    #
    @28
    @17
    @1
    cr
    wcel
    @29
    @28
    wa
    @20
    @1
    sinbnd
    syl
    simprd
    adantl
    leexp2rd
    itgle
    wph
    @12
    @8
    @5
    wceq
    @16
    vn
    @3
    vx
    @0
    @2
    vn
    cv
    #
    cexp
    co
    #
    citg
    #
    @5
    cn0
    cI
    @30
    @3
    wceq
    #
    vx
    @0
    @31
    @4
    @33
    @31
    @4
    wceq
    @17
    @30
    @3
    @2
    cexp
    oveq2
    adantr
    itgeq2dv
    wallispilem1.1
    vx
    @0
    @4
    itgex
    fvmpt
    syl
    wph
    @15
    @9
    @7
    wceq
    wallispilem1.2
    vn
    cN
    @32
    @7
    cn0
    cI
    @30
    cN
    wceq
    #
    vx
    @0
    @31
    @6
    @34
    @31
    @6
    wceq
    @17
    @30
    cN
    @2
    cexp
    oveq2
    adantr
    itgeq2dv
    wallispilem1.1
    vx
    @0
    @6
    itgex
    fvmpt
    syl
    3brtr4d
end
