include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "cminusg.mm"
include "wcel.mm"
include "eldifad.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodvnegcl.mm"
include "clss.mm"
include "cpr.mm"
include "lspprcl.mm"
include "lssneln0.mm"
include "wne.mm"
include "lspindpi.mm"
include "simpld.mm"
include "lspsnne1.mm"
include "necomd.mm"
include "lspexchn2.mm"
include "wa.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "3syl.mm"
include "adantr.mm"
include "grpinvinv.mm"
include "simpr.mm"
include "lssvnegcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "mtand.mm"
include "lspsnneg.mm"
include "neeqtrrd.mm"
include "cdif.mm"
include "grpinvnzcl.mm"
include "baerlem5a.mm"
include "grpsubinv.mm"
include "oveq1d.mm"
include "ineq12d.mm"
include "3eqtrd.mm"
include "baerlem5b.mm"
include "eqcomd.mm"
include "jca.mm"

theorem baerlem5abmN
  let wph: wff ph
  let c.pl: class .+
  let c.po: class .(+)
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume baerlem3.v: |- V = ( Base ` W )
  assume baerlem3.m: |- .- = ( -g ` W )
  assume baerlem3.o: |- .0. = ( 0g ` W )
  assume baerlem3.s: |- .(+) = ( LSSum ` W )
  assume baerlem3.n: |- N = ( LSpan ` W )
  assume baerlem3.w: |- ( ph -> W e. LVec )
  assume baerlem3.x: |- ( ph -> X e. V )
  assume baerlem3.c: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume baerlem3.d: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume baerlem3.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume baerlem3.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume baerlem5a.p: |- .+ = ( +g ` W )


  assert |- ( ph -> ( ( N ` { ( X .- ( Y .- Z ) ) } ) = ( ( ( N ` { ( X .- Y ) } ) .(+) ( N ` { Z } ) ) i^i ( ( N ` { ( X .+ Z ) } ) .(+) ( N ` { Y } ) ) ) /\ ( N ` { ( Y .- Z ) } ) = ( ( ( N ` { Y } ) .(+) ( N ` { Z } ) ) i^i ( ( N ` { ( X .- ( Y .- Z ) ) } ) .(+) ( N ` { X } ) ) ) ) )

  proof
    wph
    cX
    cY
    cZ
    c.mi
    co
    #
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    cZ
    c.pl
    co
    #
    csn
    #
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cin
    #
    wceq
    @0
    csn
    #
    cN
    cfv
    #
    @10
    @5
    c.po
    co
    #
    @3
    cX
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cin
    #
    wceq
    wph
    @3
    cX
    cY
    cZ
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    @4
    @20
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    @20
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    @10
    c.po
    co
    #
    cin
    @12
    wph
    @2
    @23
    cN
    wph
    @1
    @22
    wph
    @0
    @21
    cX
    c.mi
    wph
    cY
    cV
    wcel
    cZ
    cV
    wcel
    #
    @0
    @21
    wceq
    wph
    cY
    cV
    c.0
    csn
    #
    baerlem3.y
    eldifad
    #
    wph
    cZ
    cV
    @32
    baerlem3.z
    eldifad
    #
    cV
    c.pl
    cW
    @19
    c.mi
    cY
    cZ
    baerlem3.v
    baerlem5a.p
    @19
    eqid
    #
    baerlem3.m
    grpsubval
    syl2anc
    #
    oveq2d
    sneqd
    fveq2d
    wph
    c.pl
    c.po
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    @20
    baerlem3.v
    baerlem3.m
    baerlem3.o
    baerlem3.s
    baerlem3.n
    baerlem3.w
    baerlem3.x
    wph
    cN
    cV
    cW
    @20
    cX
    cY
    baerlem3.v
    baerlem3.n
    baerlem3.w
    wph
    cW
    clmod
    wcel
    #
    @31
    @20
    cV
    wcel
    wph
    cW
    clvec
    wcel
    #
    @37
    baerlem3.w
    cW
    lveclmod
    #
    syl
    #
    @34
    @19
    cV
    cW
    cZ
    baerlem3.v
    @35
    lmodvnegcl
    syl2anc
    baerlem3.x
    @33
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    baerlem3.v
    baerlem3.o
    baerlem3.n
    baerlem3.w
    wph
    cW
    clss
    cfv
    #
    cY
    cZ
    cpr
    cN
    cfv
    cV
    cW
    cX
    c.0
    baerlem3.v
    baerlem3.o
    @41
    eqid
    #
    @40
    wph
    @41
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    @42
    baerlem3.n
    @40
    @33
    @34
    lspprcl
    baerlem3.x
    baerlem3.c
    lssneln0
    @33
    wph
    @16
    @10
    wne
    @16
    @5
    wne
    wph
    cN
    cV
    cW
    cX
    cY
    cZ
    baerlem3.v
    baerlem3.n
    baerlem3.w
    baerlem3.x
    @33
    @34
    baerlem3.c
    lspindpi
    simpld
    lspsnne1
    wph
    @20
    cY
    cX
    cpr
    cN
    cfv
    #
    wcel
    #
    cZ
    @43
    wcel
    wph
    cN
    cV
    cW
    cX
    cZ
    cY
    baerlem3.v
    baerlem3.n
    baerlem3.w
    baerlem3.x
    @34
    @33
    wph
    cN
    cV
    cW
    cZ
    cY
    c.0
    baerlem3.v
    baerlem3.o
    baerlem3.n
    baerlem3.w
    baerlem3.z
    @33
    wph
    @10
    @5
    baerlem3.d
    necomd
    lspsnne1
    baerlem3.c
    lspexchn2
    wph
    @44
    wa
    #
    @20
    @19
    cfv
    #
    cZ
    @43
    @45
    cW
    cgrp
    wcel
    #
    @31
    @46
    cZ
    wceq
    wph
    @47
    @44
    wph
    @38
    @37
    @47
    baerlem3.w
    @39
    cW
    lmodgrp
    3syl
    #
    adantr
    wph
    @31
    @44
    @34
    adantr
    cV
    cW
    @19
    cZ
    baerlem3.v
    @35
    grpinvinv
    syl2anc
    @45
    @37
    @43
    @41
    wcel
    #
    @44
    @46
    @43
    wcel
    wph
    @37
    @44
    @40
    adantr
    wph
    @49
    @44
    wph
    @41
    cN
    cV
    cW
    cY
    cX
    baerlem3.v
    @42
    baerlem3.n
    @40
    @33
    baerlem3.x
    lspprcl
    adantr
    wph
    @44
    simpr
    @41
    @43
    @19
    cW
    @20
    @42
    @35
    lssvnegcl
    syl3anc
    eqeltrrd
    mtand
    lspexchn2
    #
    wph
    @10
    @5
    @25
    baerlem3.d
    wph
    @37
    @31
    @25
    @5
    wceq
    @40
    @34
    @19
    cN
    cV
    cW
    cZ
    baerlem3.v
    @35
    baerlem3.n
    lspsnneg
    syl2anc
    #
    neeqtrrd
    #
    baerlem3.y
    wph
    @47
    cZ
    cV
    @32
    cdif
    #
    wcel
    @20
    @53
    wcel
    @48
    baerlem3.z
    cV
    cW
    @19
    cZ
    c.0
    baerlem3.v
    baerlem3.o
    @35
    grpinvnzcl
    syl2anc
    #
    baerlem5a.p
    baerlem5a
    wph
    @26
    @6
    @30
    @11
    wph
    @25
    @5
    @4
    c.po
    @51
    oveq2d
    wph
    @29
    @9
    @10
    c.po
    wph
    @28
    @8
    cN
    wph
    @27
    @7
    wph
    cV
    c.pl
    cW
    c.mi
    @19
    cX
    cZ
    baerlem3.v
    baerlem5a.p
    baerlem3.m
    @35
    @48
    baerlem3.x
    @34
    grpsubinv
    sneqd
    fveq2d
    oveq1d
    ineq12d
    3eqtrd
    wph
    @14
    @21
    csn
    #
    cN
    cfv
    @10
    @25
    c.po
    co
    #
    @24
    @16
    c.po
    co
    #
    cin
    @18
    wph
    @13
    @55
    cN
    wph
    @0
    @21
    @36
    sneqd
    fveq2d
    wph
    c.pl
    c.po
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    @20
    baerlem3.v
    baerlem3.m
    baerlem3.o
    baerlem3.s
    baerlem3.n
    baerlem3.w
    baerlem3.x
    @50
    @52
    baerlem3.y
    @54
    baerlem5a.p
    baerlem5b
    wph
    @56
    @15
    @57
    @17
    wph
    @25
    @5
    @10
    c.po
    @51
    oveq2d
    wph
    @24
    @3
    @16
    c.po
    wph
    @23
    @2
    cN
    wph
    @22
    @1
    wph
    @21
    @0
    cX
    c.mi
    wph
    @0
    @21
    @36
    eqcomd
    oveq2d
    sneqd
    fveq2d
    oveq1d
    ineq12d
    3eqtrd
    jca
end
