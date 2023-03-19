include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cminusg.mm"
include "cin.mm"
include "wcel.mm"
include "wceq.mm"
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

theorem baerlem5amN
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


  assert |- ( ph -> ( N ` { ( X .- ( Y .- Z ) ) } ) = ( ( ( N ` { ( X .- Y ) } ) .(+) ( N ` { Z } ) ) i^i ( ( N ` { ( X .+ Z ) } ) .(+) ( N ` { Y } ) ) ) )

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
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    #
    @4
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    @4
    c.mi
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
    @8
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
    @14
    c.po
    co
    #
    cin
    wph
    @2
    @7
    cN
    wph
    @1
    @6
    wph
    @0
    @5
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
    @5
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
    @23
    baerlem3.z
    eldifad
    #
    cV
    c.pl
    cW
    @3
    c.mi
    cY
    cZ
    baerlem3.v
    baerlem5a.p
    @3
    eqid
    #
    baerlem3.m
    grpsubval
    syl2anc
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
    @4
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
    @4
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
    @22
    @4
    cV
    wcel
    wph
    cW
    clvec
    wcel
    #
    @27
    baerlem3.w
    cW
    lveclmod
    #
    syl
    #
    @25
    @3
    cV
    cW
    cZ
    baerlem3.v
    @26
    lmodvnegcl
    syl2anc
    baerlem3.x
    @24
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
    @31
    eqid
    #
    @30
    wph
    @31
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    @32
    baerlem3.n
    @30
    @24
    @25
    lspprcl
    baerlem3.x
    baerlem3.c
    lssneln0
    @24
    wph
    cX
    csn
    cN
    cfv
    #
    @14
    wne
    @33
    @16
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
    @24
    @25
    baerlem3.c
    lspindpi
    simpld
    lspsnne1
    wph
    @4
    cY
    cX
    cpr
    cN
    cfv
    #
    wcel
    #
    cZ
    @34
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
    @25
    @24
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
    @24
    wph
    @14
    @16
    baerlem3.d
    necomd
    lspsnne1
    baerlem3.c
    lspexchn2
    wph
    @35
    wa
    #
    @4
    @3
    cfv
    #
    cZ
    @34
    @36
    cW
    cgrp
    wcel
    #
    @22
    @37
    cZ
    wceq
    wph
    @38
    @35
    wph
    @28
    @27
    @38
    baerlem3.w
    @29
    cW
    lmodgrp
    3syl
    #
    adantr
    wph
    @22
    @35
    @25
    adantr
    cV
    cW
    @3
    cZ
    baerlem3.v
    @26
    grpinvinv
    syl2anc
    @36
    @27
    @34
    @31
    wcel
    #
    @35
    @37
    @34
    wcel
    wph
    @27
    @35
    @30
    adantr
    wph
    @40
    @35
    wph
    @31
    cN
    cV
    cW
    cY
    cX
    baerlem3.v
    @32
    baerlem3.n
    @30
    @24
    baerlem3.x
    lspprcl
    adantr
    wph
    @35
    simpr
    @31
    @34
    @3
    cW
    @4
    @32
    @26
    lssvnegcl
    syl3anc
    eqeltrrd
    mtand
    lspexchn2
    wph
    @14
    @16
    @9
    baerlem3.d
    wph
    @27
    @22
    @9
    @16
    wceq
    @30
    @25
    @3
    cN
    cV
    cW
    cZ
    baerlem3.v
    @26
    baerlem3.n
    lspsnneg
    syl2anc
    #
    neeqtrrd
    baerlem3.y
    wph
    @38
    cZ
    cV
    @23
    cdif
    #
    wcel
    @4
    @42
    wcel
    @39
    baerlem3.z
    cV
    cW
    @3
    cZ
    c.0
    baerlem3.v
    baerlem3.o
    @26
    grpinvnzcl
    syl2anc
    baerlem5a.p
    baerlem5a
    wph
    @10
    @17
    @15
    @21
    wph
    @9
    @16
    @8
    c.po
    @41
    oveq2d
    wph
    @13
    @20
    @14
    c.po
    wph
    @12
    @19
    cN
    wph
    @11
    @18
    wph
    cV
    c.pl
    cW
    c.mi
    @3
    cX
    cZ
    baerlem3.v
    baerlem5a.p
    baerlem3.m
    @26
    @39
    baerlem3.x
    @25
    grpsubinv
    sneqd
    fveq2d
    oveq1d
    ineq12d
    3eqtrd
end
