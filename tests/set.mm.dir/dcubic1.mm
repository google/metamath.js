include "c3.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cmin.mm"
include "oveq1d.mm"
include "cc.mm"
include "wcel.mm"
include "cdiv.mm"
include "halfcld.mm"
include "eqeltrd.mm"
include "binom2sub.mm"
include "syl2anc.mm"
include "2cnd.mm"
include "mul12d.mm"
include "oveq2d.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "eqtrd.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "sqcld.mm"
include "cn0.mm"
include "3cn.mm"
include "3ne0.mm"
include "divcld.mm"
include "3nn0.mm"
include "expcl.mm"
include "sylancl.mm"
include "addcld.mm"
include "mulcld.mm"
include "addsubd.mm"
include "add32d.mm"
include "2timesd.mm"
include "eqtr4d.mm"
include "3eqtr2d.mm"
include "subdid.mm"
include "sqvald.mm"
include "mulassd.mm"
include "3eqtr4d.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subsub4d.mm"
include "npncan2.mm"
include "dcubic1lem.mm"
include "mpbird.mm"

theorem dcubic1
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vu: setvar u
  let cU: class U
  assume dcubic.c: |- ( ph -> P e. CC )
  assume dcubic.d: |- ( ph -> Q e. CC )
  assume dcubic.x: |- ( ph -> X e. CC )
  assume dcubic.t: |- ( ph -> T e. CC )
  assume dcubic.3: |- ( ph -> ( T ^ 3 ) = ( G - N ) )
  assume dcubic.g: |- ( ph -> G e. CC )
  assume dcubic.2: |- ( ph -> ( G ^ 2 ) = ( ( N ^ 2 ) + ( M ^ 3 ) ) )
  assume dcubic.m: |- ( ph -> M = ( P / 3 ) )
  assume dcubic.n: |- ( ph -> N = ( Q / 2 ) )
  assume dcubic.0: |- ( ph -> T =/= 0 )
  assume dcubic1.x: |- ( ph -> X = ( T - ( M / T ) ) )


  assert |- ( ph -> ( ( X ^ 3 ) + ( ( P x. X ) + Q ) ) = 0 )

  proof
    wph
    cX
    c3
    cexp
    co
    cP
    cX
    cmul
    co
    cQ
    caddc
    co
    caddc
    co
    cc0
    wceq
    cT
    c3
    cexp
    co
    #
    c2
    cexp
    co
    #
    cQ
    @0
    cmul
    co
    #
    cM
    c3
    cexp
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cc0
    wceq
    wph
    @5
    c2
    cN
    c2
    cexp
    co
    #
    cmul
    co
    #
    @3
    caddc
    co
    #
    cQ
    cG
    cmul
    co
    #
    cmin
    co
    #
    @9
    @8
    cmin
    co
    #
    caddc
    co
    #
    cc0
    wph
    @1
    @10
    @4
    @11
    caddc
    wph
    @1
    @6
    @3
    caddc
    co
    #
    @9
    cmin
    co
    #
    @6
    caddc
    co
    #
    @13
    @6
    caddc
    co
    #
    @9
    cmin
    co
    @10
    wph
    @1
    cG
    cN
    cmin
    co
    #
    c2
    cexp
    co
    #
    cG
    c2
    cexp
    co
    #
    c2
    cG
    cN
    cmul
    co
    cmul
    co
    #
    cmin
    co
    #
    @6
    caddc
    co
    #
    @15
    wph
    @0
    @17
    c2
    cexp
    dcubic.3
    oveq1d
    wph
    cG
    cc
    wcel
    cN
    cc
    wcel
    @18
    @22
    wceq
    dcubic.g
    wph
    cN
    cQ
    c2
    cdiv
    co
    #
    cc
    dcubic.n
    wph
    cQ
    dcubic.d
    halfcld
    eqeltrd
    #
    cG
    cN
    binom2sub
    syl2anc
    wph
    @21
    @14
    @6
    caddc
    wph
    @19
    @13
    @20
    @9
    cmin
    dcubic.2
    wph
    @20
    cG
    c2
    cN
    cmul
    co
    #
    cmul
    co
    cG
    cQ
    cmul
    co
    @9
    wph
    c2
    cG
    cN
    wph
    2cnd
    #
    dcubic.g
    @24
    mul12d
    wph
    @25
    cQ
    cG
    cmul
    wph
    @25
    c2
    @23
    cmul
    co
    cQ
    wph
    cN
    @23
    c2
    cmul
    dcubic.n
    oveq2d
    wph
    cQ
    c2
    dcubic.d
    @26
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divcan2d
    eqtrd
    #
    oveq2d
    wph
    cG
    cQ
    dcubic.g
    dcubic.d
    mulcomd
    3eqtrd
    oveq12d
    oveq1d
    3eqtrd
    wph
    @13
    @6
    @9
    wph
    @6
    @3
    wph
    cN
    @24
    sqcld
    #
    wph
    cM
    cc
    wcel
    c3
    cn0
    wcel
    @3
    cc
    wcel
    wph
    cM
    cP
    c3
    cdiv
    co
    cc
    dcubic.m
    wph
    cP
    c3
    dcubic.c
    c3
    cc
    wcel
    wph
    3cn
    a1i
    c3
    cc0
    wne
    wph
    3ne0
    a1i
    divcld
    eqeltrd
    3nn0
    cM
    c3
    expcl
    sylancl
    #
    addcld
    @28
    wph
    cQ
    cG
    dcubic.d
    dcubic.g
    mulcld
    #
    addsubd
    wph
    @16
    @8
    @9
    cmin
    wph
    @16
    @6
    @6
    caddc
    co
    #
    @3
    caddc
    co
    @8
    wph
    @6
    @3
    @6
    @28
    @29
    @28
    add32d
    wph
    @7
    @31
    @3
    caddc
    wph
    @6
    @28
    2timesd
    oveq1d
    eqtr4d
    oveq1d
    3eqtr2d
    wph
    @4
    @9
    @7
    cmin
    co
    #
    @3
    cmin
    co
    @11
    wph
    @2
    @32
    @3
    cmin
    wph
    cQ
    @17
    cmul
    co
    @9
    cQ
    cN
    cmul
    co
    #
    cmin
    co
    @2
    @32
    wph
    cQ
    cG
    cN
    dcubic.d
    dcubic.g
    @24
    subdid
    wph
    @0
    @17
    cQ
    cmul
    dcubic.3
    oveq2d
    wph
    @7
    @33
    @9
    cmin
    wph
    @7
    c2
    cN
    cN
    cmul
    co
    #
    cmul
    co
    @25
    cN
    cmul
    co
    @33
    wph
    @6
    @34
    c2
    cmul
    wph
    cN
    @24
    sqvald
    oveq2d
    wph
    c2
    cN
    cN
    @26
    @24
    @24
    mulassd
    wph
    @25
    cQ
    cN
    cmul
    @27
    oveq1d
    3eqtr2d
    oveq2d
    3eqtr4d
    oveq1d
    wph
    @9
    @7
    @3
    @30
    wph
    c2
    cc
    wcel
    @6
    cc
    wcel
    @7
    cc
    wcel
    2cn
    @28
    c2
    @6
    mulcl
    sylancr
    #
    @29
    subsub4d
    eqtrd
    oveq12d
    wph
    @8
    cc
    wcel
    @9
    cc
    wcel
    @12
    cc0
    wceq
    wph
    @7
    @3
    @35
    @29
    addcld
    @30
    @8
    @9
    npncan2
    syl2anc
    eqtrd
    wph
    cP
    cQ
    cT
    cT
    cG
    cM
    cN
    cX
    dcubic.c
    dcubic.d
    dcubic.x
    dcubic.t
    dcubic.3
    dcubic.g
    dcubic.2
    dcubic.m
    dcubic.n
    dcubic.0
    dcubic.t
    dcubic.0
    dcubic1.x
    dcubic1lem
    mpbird
end
